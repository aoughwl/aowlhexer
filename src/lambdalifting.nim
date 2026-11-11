#
#
#           Hexer Compiler
#        (c) Copyright 2025 Andreas Rumpf
#
#    See the file "license.txt", included in this
#    distribution, for details about the copyright.
#

##[
Lambda lifting uses multiple passes:

- Determine which local variables cross proc boundaries. Map these to an environment.
  An environment is a scope that is allocated on the heap.
- Each usage of such a local becomes `env.local` but the `env` is not always the same:
  The outer env is itself a local variable, the inner env is a proc parameter.
- Procs that use a local variable that crosses a proc boundary are marked as "closure"
  ("uses environment").
- **Usages** of closure procs are turned from `fn` to `(fn, env)` and these tuple calls are
  turned from `(fn, env)(args)` to `fn(args, env)`. The tuple creation/unpacking can
  be optimized further.
- If all usages of closure procs do not escape, the environment can be allocated on
  the stack. As an approximation, closure procs do not escape if they are only used
  as the `fn` value in a function call `fn(args)`.
- A single indirection might not be enough. Consider:

```nim
  proc outerA =
    var a, b: int
    proc outerB =
      proc innerA = use(a)
      proc innerB = use(b); innerA()
      innerB()
```

Here `outerB` is also a closure.

A routine's captured locals live in that routine's own environment, and every
activation has its own. A routine has just one parameter for an environment, so
one that creates an environment and also reaches further out keeps the parameter
in it: see `genObjectTypes`.

A local declared in the body of a loop is a new variable on every iteration, like
every `let` says, so a closure made in one iteration keeps that iteration's value:
such a body is a level of its own here, with an environment made as it is entered.
It is a "routine" on `procStack` called a loop scope, except that its code is in
the routine around it, whose locals it reaches directly. See `trWhile`.

]##

import std / [assertions, sets, tables, hashes, syncio]
include ".." / lib / nifprelude
include ".." / lib / compat2
import ".." / lib / symparser
import ".." / nimony / [nimony_model, decls, programs, typenav, expreval, xints, builtintypes, langmodes, renderer, reporters, typeprops]
import hsizeof
import hexer_context, passes
include ".." / nimony / nif_annotations
import coro_transform
# Bring the iter-value tuple constants/helpers into scope as
# unqualified names. `ResultParamName` / `CallerParamName` are the
# canonical names; lambdalifting's old aliases (`IterResultParamName`,
# `IterCallerParamName`) are gone — they were the same strings.
# `BareRootObjName` is the real `RootObj` (the env-slot type); the
# misleadingly-named `RootObjName` over in coro_transform is
# `CoroutineBase` and is NOT the right thing for the env slot. Don't
# confuse them.

type
  EnvMode = enum
    EnvIsLocal, EnvIsParam
  CurrentEnv = object
    s: SymId
    typ: SymId
    mode: EnvMode
    needsHeap: bool

  EnvField = object
    objType: SymId
    field: SymId
    typ: Cursor

  Context = object
    counter: int
    typeCache: TypeCache
    thisModuleSuffix: string
    procStack: seq[SymId]
    dest: TokenBuf
    closureProcs, createsEnv, escapes: HashSet[SymId]
    capturers: HashSet[SymId]
      ## Routines that must really be handed an environment, because they, or a
      ## routine nested in them, reach a local of an enclosing routine. The rest
      ## of `closureProcs` is `.closure` by pragma only.
    procParent: Table[SymId, SymId]
    procRefs: seq[(SymId, SymId)]
      ## (user, used): a routine mentions a nested routine.
    envUp: Table[SymId, SymId]
      ## env type -> its link to the environment of the enclosing routine.
    loopScopes: HashSet[SymId]
      ## The entries of `procStack` that are the body of a loop, not a routine.
    loopEnvLocal: Table[SymId, SymId]
      ## loop scope -> the local holding its environment.
    localToEnv: Table[SymId, EnvField]
    env: CurrentEnv
    hasClosures: bool
    sweepSeen, liftedProcs, capturedSyms, keptResults: HashSet[SymId]
    declDepth: Table[SymId, int]
      ## local or parameter -> how many routines it is nested in. The type cache's
      ## `crossedProc` does not count the routine of a local declared in a nested
      ## scope of it: `for`, `block` and so on.
    declLog: seq[(SymId, int)]
      ## What a routine's declarations replaced in `declDepth`: an inner routine's
      ## `ii.N` may be spelled like one of the routine around it.
    coroCtx: coro_transform.Context
      ## Shadow `coro_transform.Context` used to drive `.closure` iter
      ## state-machine generation. We loan our `typeCache` to it via
      ## `swap` while `transformCoroutineDecl` runs, then swap back.
      ## `coroTypes` and `shouldPublish` accumulate here across all
      ## iters in the module and get flushed in `elimLambdas`.

proc tr(c: var Context; dest: var TokenBuf; n: var Cursor)
  {.ensuresNif: addedAny(dest).}

proc isClosureIterDecl(n: Cursor): bool =
  ## True if `n` is at an `(iterator :sym …)` whose pragmas carry
  ## `.closure`. Used by pass 1 (set `hasClosures`) and pass 2 (route
  ## to `transformClosureIter`).
  if n.stmtKind != IteratorS: return false
  var m = n
  inc m   # past iterator tag
  for _ in 0..<ProcPragmasPos:
    skip m
  hasPragma(m, ClosureP)

proc isRoutineDecl(n: Cursor): bool =
  n.stmtKind in {ProcS, FuncS, MethodS, ConverterS, IteratorS, MacroS, TemplateS} and
    n.firstSon.kind == SymbolDef

proc scanCapture(n: var Cursor; depth: int; onlyDirect: bool; decls, own: var HashSet[SymId]; found: var bool) =
  ## Is a local declared outside of every routine used inside of one? With
  ## `onlyDirect` only the locals that are direct sons of the tree being asked about
  ## count: the others can be left to the statement around them.
  case n.kind
  of Symbol:
    if depth > 0 and decls.contains(n.symId) and not own.contains(n.symId):
      found = true
    inc n
  of ParLe:
    if depth > 0 and n.substructureKind == ParamU and n.firstSon.kind == SymbolDef:
      own.incl n.firstSon.symId
    if isRoutineDecl(n):
      var inner = initHashSet[SymId]()
      inc n
      while n.hasMore:
        scanCapture n, depth + 1, onlyDirect, decls, inner, found
      inc n
    elif n.stmtKind in {VarS, LetS, CursorS, PatternvarS, ResultS, GvarS, GletS, TvarS, TletS}:
      let isPlain = n.stmtKind in {VarS, LetS, CursorS, PatternvarS, ResultS}
      let s = n.firstSon
      if s.kind == SymbolDef:
        if depth > 0:
          own.incl s.symId
        elif isPlain and not onlyDirect:
          decls.incl s.symId
      inc n
      while n.hasMore:
        scanCapture n, depth, onlyDirect, decls, own, found
      inc n
    else:
      inc n
      while n.hasMore:
        scanCapture n, depth, onlyDirect, decls, own, found
      inc n
  else:
    inc n

proc capturesToplevelLocal(n: Cursor): bool =
  var n = n
  var decls = initHashSet[SymId]()
  var own = initHashSet[SymId]()
  result = false
  scanCapture n, 0, false, decls, own, result

proc trWhile(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## Pass 1 of a loop, a `while` or the `corofor` of a closure iterator. A body with
  ## locals that a routine captures gets a loop scope, named for pass 2 in a
  ## `(comment <scope>)` at the start of the body.
  copyInto dest, n:
    tr c, dest, n # condition, or the iterator's call
    var blockClose = false
    if n.stmtKind == BlockS:
      # the body of a `corofor` is a block around the statements
      dest.takeToken n
      dest.takeTree n # label
      blockClose = true
    if c.procStack.len > 0 and n.stmtKind == StmtsS and capturesToplevelLocal(n):
      let scope = pool.syms.getOrIncl("`lscope." & $c.counter & "." & c.thisModuleSuffix)
      inc c.counter
      c.hasClosures = true
      c.loopScopes.incl scope
      c.procParent[scope] = c.procStack[c.procStack.len-1]
      c.procStack.add scope
      let info = n.info
      dest.add n
      inc n
      dest.copyIntoKind CommentS, info:
        dest.addSymUse scope, info
      while n.hasMore:
        tr c, dest, n
      dest.takeParRi n
      discard c.procStack.pop()
    if blockClose:
      while n.hasMore:
        tr c, dest, n
      dest.takeParRi n
    while n.hasMore:
      tr c, dest, n

proc trSons(c: var Context; dest: var TokenBuf; n: var Cursor) =
  copyInto dest, n:
    while n.hasMore:
      tr(c, dest, n)

proc noteDecl(c: var Context; s: SymId) =
  c.declLog.add (s, c.declDepth.getOrDefault(s, -1))
  c.declDepth[s] = c.procStack.len

proc trLocal(c: var Context; dest: var TokenBuf; n: var Cursor) =
  let kind = n.symKind
  noteDecl c, n.firstSon.symId
  copyInto dest, n:
    c.typeCache.takeLocalHeader(dest, n, kind)
    tr(c, dest, n)

proc trProc(c: var Context; dest: var TokenBuf; n: var Cursor) =
  #c.typeCache.openScope(ProcScope)
  let decl = n
  copyInto dest, n:
    let symId = n.symId
    if c.procStack.len > 0:
      c.procParent[symId] = c.procStack[c.procStack.len-1]
    c.procStack.add(symId)
    let declMark = c.declLog.len
    var isConcrete = true # assume it is concrete
    for i in 0..<BodyPos:
      if i == ParamsPos:
        c.typeCache.openProcScope(symId, decl, n)
        c.typeCache.registerParams(symId, decl, n)
        if n.substructureKind == ParamsU:
          var p = n
          inc p
          while p.hasMore:
            noteDecl c, p.firstSon.symId
            skip p
      elif i == TypevarsPos:
        isConcrete = n.substructureKind != TypevarsU
      elif i == ProcPragmasPos:
        if hasPragma(n, ClosureP):
          c.closureProcs.incl symId
          c.escapes.incl symId
          c.hasClosures = true
      takeTree dest, n
    if isConcrete:
      tr(c, dest, n)
    else:
      takeTree dest, n
    discard c.procStack.pop()
    while c.declLog.len > declMark:
      let e = c.declLog.pop()
      c.declDepth[e[0]] = e[1]
  c.typeCache.closeScope()

proc envTypeForProc(c: Context; procId: SymId): SymId =
  let s = extractVersionedBasename(pool.syms[procId])
  result = pool.syms.getOrIncl(s & ".env." & c.thisModuleSuffix)

proc envKey(owner, local: SymId): SymId =
  ## A local's symbol is not unique in a module: the temps of an inlined iterator,
  ## `ii.N`, start over in every routine. Two routines capturing such a temp must
  ## not share a slot, or the second reaches for the first one's environment.
  pool.syms.getOrIncl(pool.syms[local] & "@" & pool.syms[owner])

proc envField(c: Context; local: SymId): EnvField =
  ## The slot of a local of the routine being lowered, if it has one.
  if c.capturedSyms.contains(local) and c.procStack.len > 0:
    result = c.localToEnv.getOrDefault(envKey(c.procStack[c.procStack.len-1], local))
  else:
    result = default(EnvField)

proc localToField(c: var Context; n: Cursor; owner, local, typ: SymId): SymId =
  let key = envKey(owner, local)
  if c.localToEnv.hasKey(key):
    result = c.localToEnv.getOrQuit(key).field
  else:
    c.capturedSyms.incl local
    var name = pool.syms[local]
    extractBasename name
    name.add "`f."
    name.add $c.counter
    inc c.counter
    name.add "."
    name.add c.thisModuleSuffix
    result = pool.syms.getOrIncl(name)
    c.localToEnv[key] = EnvField(objType: typ, field: result, typ: c.typeCache.getType(n))

proc trCall(c: var Context; dest: var TokenBuf; n: var Cursor) =
  dest.add n
  inc n
  if n.kind == Symbol and c.typeCache.getLocalInfo(n.symId).kind in {ProcY, FuncY, IteratorY, ConverterY, MethodY}:
    # if a closure proc is called, we don't want to see it as "escaping".
    if c.procStack.len > 0:
      c.procRefs.add (c.procStack[c.procStack.len-1], n.symId)
    dest.add n
    inc n
  # Any other callee is a value like every other: a closure held in a local of
  # an enclosing routine has to become an environment access here, or the lifted
  # routine would name a local of a routine it is no longer inside.
  while n.hasMore:
    tr(c, dest, n)
  dest.takeParRi(n)

proc itertypeNeedsTuple(n: Cursor): bool {.inline.} =
  ## True when an itertype's pragmas tag it as a `.closure` iter (Nim-style
  ## resumable, ref-based shared env). `.passive` iters keep the existing
  ## non-ref CPS lowering: cps's `trProctype` rewrites their itertype to a
  ## plain function pointer with the wrapper signature, no tuple wrap.
  n.typeKind == ItertypeT and procHasPragma(n, ClosureP)

proc trNil(c: var Context; dest: var TokenBuf; n: var Cursor) =
  let info = n.info
  inc n
  # `(nil <Type>)` for a closure proctype OR itertype (.closure / .passive)
  # lowers to a `{fnptr, env}` tuple constructor — that's the runtime shape
  # of Nim closures and of our wrapper-signature iter values.
  let isIter = n.hasMore and itertypeNeedsTuple(n)
  let isCloseable = n.hasMore and (isIter or procHasPragma(n, ClosureP))
  if isIter:
    c.hasClosures = true
    dest.copyIntoKind TupconstrX, info:
      # rewrite the inner itertype to its wrapper-shape tuple
      emitIterTupleTypeFromParams(dest, n, info)
      if n.hasMore: skip n # might have another nil value
      dest.addParPair NilX, info
      dest.addParPair NilX, info
    skipParRi n
  elif isCloseable:
    # nil closure must be a tuple:
    c.hasClosures = true
    dest.copyIntoKind TupconstrX, info:
      dest.takeTree n # type
      if n.hasMore: skip n # might have another nil value
      dest.addParPair NilX, info
      dest.addParPair NilX, info
    skipParRi n
  else:
    dest.addParLe NilX, n.info
    while n.hasMore: takeTree dest, n
    dest.takeParRi n

proc tr(c: var Context; dest: var TokenBuf; n: var Cursor) =
  case n.kind
  of DotToken, UnknownToken, EofToken, Ident, SymbolDef,
     IntLit, UIntLit, FloatLit, CharLit, StringLit:
    takeTree dest, n
  of Symbol:
    let loc = c.typeCache.getLocalInfo(n.symId)
    if loc.kind in {ParamY, LetY, VarY, ResultY}:
      let declaredAt = c.declDepth.getOrDefault(n.symId, -1)
      let cross = if declaredAt < 0: 0 else: c.procStack.len - declaredAt
      # Loop scopes are in the routine around them: only a routine is a capture.
      var crossesRoutine = false
      for i in max(0, c.procStack.len - cross) ..< c.procStack.len:
        if not c.loopScopes.contains(c.procStack[i]):
          crossesRoutine = true
      if crossesRoutine:
        if declaredAt == 0:
          # No routine owns it, so no environment can hold it: `hoistToplevel` is
          # there so that this does not happen. Going on would give the routine an
          # environment of its own, with a zeroed copy of the local.
          quit "Error: cannot capture `" & pool.syms[n.symId] & "`, a local of module-level code, at " &
            infoToStr(n.info)
        for i in max(0, c.procStack.len - cross) ..< c.procStack.len:
          c.closureProcs.incl(c.procStack[i])
          c.capturers.incl(c.procStack[i])
        # The local lives in the environment of the routine that declares it.
        # One environment for a whole nest cannot work: `f`'s locals would be
        # one slot shared by every activation of `f`, so with
        #
        #   proc main() =
        #     let f = proc (x: int): proc (): int {.closure.} {.closure.} =
        #       (proc (): int {.closure.} = x)
        #     let a = f(1)
        #     let b = f(2)
        #
        # `a` would answer 2. See `genObjectTypes` for how the environments link.
        let destEnv = c.procStack[max(0, c.procStack.len - 1 - cross)]
        c.createsEnv.incl destEnv
        let envType = c.envTypeForProc(destEnv)
        let fld = c.localToField(n, destEnv, n.symId, envType)
        dest.copyIntoKind EnvpX, n.info:
          dest.addSymUse envType, n.info
          dest.addSymUse fld, n.info
        inc n
      else:
        takeTree dest, n
    elif loc.kind in {ProcY, FuncY, IteratorY, ConverterY, MethodY}:
      # usage of a closure proc not within a call? --> The closure does escape:
      if c.procStack.len > 0:
        #c.escapes.incl n.symId
        c.escapes.incl c.procStack[0]
        c.procRefs.add (c.procStack[c.procStack.len-1], n.symId)
      takeTree dest, n
    else:
      takeTree dest, n
  of ParLe:
    case n.stmtKind
    of LocalDecls:
      trLocal c, dest, n
    of ProcS, FuncS, MethodS, ConverterS:
      if n.firstSon.kind == DotToken: # no name: a type, not a declaration
        takeTree dest, n
      else:
        trProc c, dest, n
    of TypeS:
      # Type alias body for an itertype must be rewritten to the wrapper-shape
      # tuple BEFORE the lifter runs (lifter is in duplifier/destroyer, which
      # is after lambdalifting and before cps). Otherwise the lifter follows
      # the alias, sees ItertypeT, marks trivial (RoutineTypes branch in
      # lifter.isTrivial), and never generates destroy/copy hooks for the
      # iter-value env slot.
      let typeStart = dest.len
      dest.takeToken n        # TypeS tag
      var typeSym = SymId(0)
      if n.kind == SymbolDef:
        typeSym = n.symId
      takeTree dest, n        # name
      takeTree dest, n        # exported
      takeTree dest, n        # typevars
      takeTree dest, n        # pragmas
      if typeSym != SymId(0) and itertypeNeedsTuple(n):
        c.hasClosures = true
        emitIterTupleTypeFromParams(dest, n, n.info)
        while n.hasMore: takeTree dest, n
        dest.takeParRi n
        programs.publish(typeSym, dest, typeStart)
      else:
        while n.hasMore: takeTree dest, n
        dest.takeParRi n
    of IteratorS:
      # `.closure` iter decls are owned by lambdalifting now (pass 2
      # generates the state machine via coro_transform). Set
      # `hasClosures` so pass 2 fires for this module even when
      # there's no other closure pressure.
      if isClosureIterDecl(n):
        c.hasClosures = true
      takeTree dest, n
    of MacroS, TemplateS, EmitS, BreakS, ContinueS,
      ForS, IncludeS, ImportS, FromimportS, ImportexceptS,
      ExportS, CommentS,
      PragmasS:
      takeTree dest, n
    of ScopeS:
      c.typeCache.openScope()
      trSons(c, dest, n)
      c.typeCache.closeScope()
    of WhileS:
      trWhile c, dest, n
    of CoroforS:
      trWhile c, dest, n
    of CallS, CmdS, BlockS, AsgnS, IfS, WhenS,
      CaseS, RetS, YldS, StmtsS, PragmaxS, InclS, ExclS, ImportasS,
      ExportexceptS, DiscardS, TryS, RaiseS, UnpackdeclS,
      AssumeS, AssertS, CallstrlitS, InfixS, PrefixS, HcallS,
      StaticstmtS, BindS, MixinS, UsingS, AsmS, DeferS,
      NoStmt:
      case n.exprKind
      of CallKinds:
        trCall c, dest, n
      of TypeofX:
        takeTree dest, n
      of NilX:
        trNil c, dest, n
      of ToClosureX:
        c.hasClosures = true
        trSons(c, dest, n)
      of KvX:
        # The key names a field, even when a captured local is spelled the same:
        # `E(n: n)` inside a closure over `n` must only rewrite the value.
        dest.add n
        inc n
        takeTree dest, n
        while n.hasMore:
          tr(c, dest, n)
        dest.takeParRi n
      of DotX:
        # So does the field of a `dot`: `e.n` beside a captured local `n`.
        dest.add n
        inc n
        tr(c, dest, n)
        while n.hasMore:
          takeTree dest, n
        dest.takeParRi n
      of ErrX, SufX, AtX, DerefX, PatX, ParX, AddrX,
        InfX, NeginfX, NanX, FalseX, TrueX, AndX, OrX, XorX,
        NotX, NegX, SizeofX, AlignofX, OffsetofX, OconstrX,
        AconstrX, BracketX, CurlyX, CurlyatX, OvfX, AddX,
        SubX, MulX, DivX, ModX, ShrX, ShlX, BitandX, BitorX,
        BitxorX, BitnotX, EqX, NeqX, LeX, LtX, CastX, ConvX,
        CchoiceX, OchoiceX, PragmaxX, QuotedX, HderefX, DdotX,
        HaddrX, NewrefX, NewobjX, TupX, TupconstrX, SetconstrX,
        TabconstrX, AshrX, BaseobjX, HconvX, DconvX, CompilesX,
        DeclaredX, DefinedX, AstToStrX, BindSymX, BindSymNameX, InstanceofX, HighX,
        LowX, UnpackX, FieldsX, FieldpairsX, EnumtostrX,
        IsmainmoduleX, DefaultobjX, DefaulttupX,
        DefaultdistinctX, Delay0X, SuspendX, ExprX, DoX,
        ArratX, TupatX, PlussetX, MinussetX, MulsetX, XorsetX,
        EqsetX, LesetX, LtsetX, InsetX, CardX, EmoveX,
        DestroyX, DupX, CopyX, WasmovedX, SinkhX, TraceX,
        InternalTypeNameX, InternalFieldPairsX, FailedX, IsX,
        EnvpX, NoExpr:
        trSons(c, dest, n)
  of ParRi:
    bug "unexpected ')' inside"

proc isClosure(typ: Cursor): bool {.inline.} = procHasPragma(typ, ClosureP)

proc mentionsClosureRoutineType(n: Cursor): bool =
  ## True when this subtree declares a `.closure` routine TYPE somewhere --
  ## the only reason a type DECLARATION needs pass-2 lowering at all.
  ## An already-lifted `(tuple (proctype ...) (ref RootObj))` does not count:
  ## recursing into one would re-wrap its inner proctype (see
  ## `isLiftedClosureTuple`).
  var n = n
  var nested = 0
  while true:
    case n.kind
    of ParLe:
      if isLiftedClosureTuple(n):
        skip n
        if nested == 0: break
      elif n.typeKind in RoutineTypes and (isClosure(n) or itertypeNeedsTuple(n)):
        return true
      else:
        inc nested
        inc n
    of ParRi:
      dec nested
      inc n
      if nested <= 0: break
    of EofToken:
      break
    else:
      inc n
      if nested == 0: break
  result = false


when false:
  proc paramsWithClosurePragma(typ: Cursor): bool =
    var typ = typ
    skip typ
    skip typ # return type
    result = hasPragma(typ, ClosureP)

const
  # Lambdalifting-specific names (not in coro_transform).
  EnvParamName = "`ep.0"

# `RootObjName` / `coroWrapperProcName` / `emitIterTupleType*` /
# `isClosureIterSym` / `isLiftedClosureTuple` now live in
# `coro_transform`. The wrapper-signature shape is owned there too, so
# both passes stay in lock-step automatically.

proc addRootRef(dest: var TokenBuf; info: PackedLineInfo)
  {.ensuresNif: addedType(dest).} =
  dest.copyIntoKind RefT, info:
    dest.addSymUse pool.syms.getOrIncl(BareRootObjName), info

type
  UntypedEnvMode = enum
    WantValue, WantAddr

proc untypedEnv(dest: var TokenBuf; info: PackedLineInfo; env: CurrentEnv; mode=WantValue)
  {.ensuresNif: addedExpr(dest).} =
  assert env.s != SymId(0)
  case env.mode
  of EnvIsLocal:
    dest.copyIntoKind CastX, info:
      if env.needsHeap:
        dest.addRootRef info
      else:
        dest.copyIntoKind PointerT, info: discard
      if mode == WantAddr:
        dest.copyIntoKind AddrX, info:
          dest.addSymUse env.s, info
      else:
        dest.addSymUse env.s, info
  of EnvIsParam:
    # the parameter already has the erased type:
    if mode == WantAddr:
      dest.copyIntoKind AddrX, info:
        dest.addSymUse env.s, info
    else:
      dest.addSymUse env.s, info

proc typedEnv(dest: var TokenBuf; info: PackedLineInfo; env: CurrentEnv)
  {.ensuresNif: addedExpr(dest).} =
  assert env.s != SymId(0)
  case env.mode
  of EnvIsLocal:
    # the local already has the full type:
    dest.addSymUse env.s, info
  of EnvIsParam:
    # the parameter has the erased type:
    dest.copyIntoKind CastX, info:
      dest.copyIntoKind (if env.needsHeap: RefT else: PtrT), info:
        dest.addSymUse env.typ, info
      dest.addSymUse env.s, info

proc envOwnerIndex(c: Context; envTyp: SymId): int =
  ## Where in `procStack` is the routine whose environment type is `envTyp`?
  result = -1
  var i = c.procStack.len - 1
  while i >= 0:
    if c.createsEnv.contains(c.procStack[i]) and c.envTypeForProc(c.procStack[i]) == envTyp:
      return i
    dec i

proc emitChildEnv(c: var Context; dest: var TokenBuf; info: PackedLineInfo; i: int)
  {.ensuresNif: addedExpr(dest).}

proc emitEnvParamOf(c: var Context; dest: var TokenBuf; info: PackedLineInfo; j: int)
  {.ensuresNif: addedExpr(dest).} =
  ## The value of `procStack[j]`'s environment parameter, seen from the routine
  ## being lifted: if `procStack[j]` has an environment, the parameter was kept
  ## in it.
  let s = c.procStack[j]
  if c.createsEnv.contains(s):
    let envTyp = c.envTypeForProc(s)
    let up = c.envUp.getOrDefault(envTyp)
    if up == SymId(0):
      dest.addParPair NilX, info
    else:
      dest.copyIntoKind DotX, info:
        dest.copyIntoKind DerefX, info:
          dest.copyIntoKind CastX, info:
            dest.copyIntoKind (if c.env.needsHeap: RefT else: PtrT), info:
              dest.addSymUse envTyp, info
            emitChildEnv c, dest, info, j
        dest.addSymUse up, info
  else:
    emitChildEnv c, dest, info, j

proc emitChildEnv(c: var Context; dest: var TokenBuf; info: PackedLineInfo; i: int) =
  ## The environment a routine directly nested in `procStack[i]` runs on: the
  ## one `procStack[i]` creates, else the one it was given itself.
  if i < c.procStack.len - 1:
    emitEnvParamOf c, dest, info, i + 1
  elif c.env.s == SymId(0):
    dest.addParPair NilX, info
  else:
    untypedEnv dest, info, c.env,
      (if not c.env.needsHeap and c.env.mode == EnvIsLocal: WantAddr else: WantValue)

proc emitLocalSlot(c: var Context; dest: var TokenBuf; local: SymId; info: PackedLineInfo): bool =
  ## Emits the access to the slot of a local of the routine being lowered, from its
  ## code or a loop scope in it, if the local has one.
  result = false
  if not c.capturedSyms.contains(local): return
  var i = c.procStack.len - 1
  while i >= 0:
    let s = c.procStack[i]
    let fld = c.localToEnv.getOrDefault(envKey(s, local))
    if fld.field != SymId(0):
      dest.copyIntoKind DotX, info:
        if i == c.procStack.len - 1:
          # For a stack environment `typedEnv` is the object itself: only a heap
          # one is dereferenced.
          if c.env.needsHeap:
            dest.copyIntoKind DerefX, info:
              dest.typedEnv info, c.env
          else:
            dest.typedEnv info, c.env
        else:
          let holder = if c.loopScopes.contains(s): c.loopEnvLocal.getOrDefault(s)
                       else: pool.syms.getOrIncl(EnvLocalName)
          if c.env.needsHeap:
            dest.copyIntoKind DerefX, info:
              dest.addSymUse holder, info
          else:
            dest.addSymUse holder, info
        dest.addSymUse fld.field, info
      return true
    if not c.loopScopes.contains(s): return
    dec i

proc emitEnvFor(c: var Context; dest: var TokenBuf; info: PackedLineInfo; target: SymId)
  {.ensuresNif: addedExpr(dest).} =
  ## The environment to hand to the routine `target`, from wherever it is used.
  ## Null when it needs none, which is what a call on a nil env expects as well.
  var i = -1
  if c.capturers.contains(target):
    let parent = c.procParent.getOrDefault(target)
    var k = c.procStack.len - 1
    while k >= 0 and parent != SymId(0):
      if c.procStack[k] == parent:
        i = k
        break
      dec k
  if i < 0:
    dest.addParPair NilX, info
  else:
    emitChildEnv c, dest, info, i

proc tre(c: var Context; dest: var TokenBuf; n: var Cursor)
  {.ensuresNif: addedAny(dest).}

# ---------------------------------------------------------------------
# Hooks installed on `coroCtx`. Lambdalifting drives the coro-transform
# pipeline for `.closure` iters only — there is no `.passive` here,
# nested procs have been lifted out of the iter body before
# coro_transform sees it, and the type-slot rewrites have already been
# done at the lambdalifting level. So most hooks are pass-through; the
# `.passive`-flavour ones are bug-guards.
# ---------------------------------------------------------------------

proc llIsPassiveProc(c: var coro_transform.Context; s: SymId): bool = false
proc llIsPassiveCall(c: var coro_transform.Context; n: Cursor): bool = false

proc llTrPassiveCall(c: var coro_transform.Context; dest: var TokenBuf;
                     n: var Cursor; target: Cursor) =
  bug "`.passive` call lowering invoked inside a `.closure` iter body"

proc llTrBug(c: var coro_transform.Context; dest: var TokenBuf; n: var Cursor) =
  bug "delay/suspend lowering invoked inside a `.closure` iter body"

proc llTakeTree(c: var coro_transform.Context; dest: var TokenBuf; n: var Cursor) =
  takeTree dest, n

proc lambdaHooks(): coro_transform.Hooks =
  coro_transform.Hooks(
    isPassiveProc: llIsPassiveProc,
    isPassiveCall: llIsPassiveCall,
    trPassiveCall: llTrPassiveCall,
    trDelay: llTrBug,
    trDelay0: llTrBug,
    trSuspend: llTrBug,
    trProctype: llTakeTree,
    trCoroutine: llTakeTree
  )

proc transformClosureIter(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## Run coro_transform's full pipeline on a `.closure` iter decl:
  ## state procs, coro frame type, wrapper proc, signature patch.
  ##
  ## State transfer: loan our `typeCache` to `coroCtx` for the
  ## duration of the call (so type lookups against locals we already
  ## registered keep working) and reclaim it after. `coroTypes` /
  ## `shouldPublish` stay on `coroCtx`; flushed by `elimLambdas`.
  swap c.coroCtx.typeCache, c.typeCache
  coro_transform.transformCoroutineDecl(c.coroCtx, dest, n)
  swap c.coroCtx.typeCache, c.typeCache

proc treLoopBody(c: var Context; dest: var TokenBuf; n: var Cursor)
  {.ensuresNif: addedAny(dest).}

proc isClosureCoroFor(c: var Context; n: Cursor): bool =
  ## Peek at a `(corofor (call <target> …) …)` to decide whether this
  ## corofor is for a `.closure` iter (lambdalifting handles) or a
  ## `.passive` iter (cps handles, lambdalifting passes through).
  ##
  ## Three target shapes reach here:
  ##   1. Symbol of an `.closure` iter decl — direct iter call.
  ##   2. Symbol of a local of iter-value type — iter VALUE call.
  ##   3. Non-Symbol expression (e.g. `(tupat g 0)`) emitted by
  ##      lambdalifting's genCall pre-extraction — iter VALUE call.
  ## `.passive` iter direct calls leave the target as Symbol of a
  ## non-`.closure` iter decl, which falls through to cps.
  assert n.stmtKind == CoroforS
  var m = n
  inc m  # past corofor tag
  if m.exprKind notin CallKinds: return false
  inc m  # past call tag
  if m.kind == Symbol and isClosureIterSym(m.symId):
    return true
  # Inspect the target's TYPE — covers iter-value locals (case 2)
  # and any non-Symbol target that nonetheless has iter-shaped type.
  let typ = c.typeCache.getType(m, {SkipAliases})
  if typ.typeKind == ItertypeT and procHasPragma(typ, ClosureP):
    return true
  if typ.typeKind == TupleT:
    var t = typ
    inc t  # past tuple tag
    if t.kind == ParLe and t.typeKind == ProctypeT and procHasPragma(t, ClosureP):
      return true
  return false

proc trClosureCoroFor(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## Expand `(corofor (call closure-iter args... (haddr forLoopVar)) (block ...))`
  ## into the trampoline. Mirrors `coro_transform.trCoroFor` but walks
  ## the body via lambdalifting's `tre` (so closure captures inside
  ## the for-loop body get rewritten to env accesses).
  let info = n.info
  inc n # skip (corofor

  # ---- first child: (call iter-or-tupat args... (haddr forLoopVar)) ----
  assert n.exprKind in CallKinds, "corofor: expected iter call as first child"
  inc n # past CallS tag
  # Extract the call target. Three shapes:
  #   1. Symbol of an iter DECL — direct call routed through its
  #      init wrapper.
  #   2. Symbol of an iter-VALUE local — pull fn-slot and env-slot
  #      out via `(tupat g 0)` / `(tupat g 1)`. The env-slot becomes
  #      the wrapper-call's `caller.env`, triggering the wrapper's
  #      reuse branch so iter state persists across loops.
  #   3. Pre-extracted expression (e.g. a `(tupat g 0)` already
  #      emitted by upstream genCall) — use verbatim and look for
  #      the trailing tupat env-arg further down.
  # Track which branch we took for the target — this is the ONLY
  # reliable signal for "does the arg list have an upstream env-arg?".
  # Probing the last arg for TupatX is unsound: a regular arg like
  # `(tupat someTuple 0)` would falsely match.
  var targetBuf = createTokenBuf(4)
  var valSymForEnv: SymId = SymId(0)  # case 2: synthesize env-arg from this
  var valInfoForEnv: PackedLineInfo = default(PackedLineInfo)
  var upstreamEnvArg = false           # case 3: env-arg is penultimate arg
  if n.kind == Symbol and isClosureIterSym(n.symId):
    targetBuf.addSymUse coro_transform.coroWrapperForExternIter(n.symId), n.info
    coro_transform.publishWrapperSignature(n.symId, c.thisModuleSuffix)
    inc n
  elif n.kind == Symbol:
    valSymForEnv = n.symId
    valInfoForEnv = n.info
    targetBuf.copyIntoKind TupatX, valInfoForEnv:
      targetBuf.addSymUse valSymForEnv, valInfoForEnv
      targetBuf.addIntLit 0, valInfoForEnv
    inc n
  else:
    upstreamEnvArg = true
    targetBuf.takeTree n

  # Cursors are stable into the source buffer — walk once to count args
  # and remember the cursor at each arg's start position; emit later
  # via `addSubtree` from those cursor copies.
  let argsStart = n
  var lastArgPos = default(Cursor)
  var penultimateArgPos = default(Cursor)
  var argCount = 0
  while n.hasMore:
    penultimateArgPos = lastArgPos
    lastArgPos = n
    skip n
    inc argCount
  skipParRi n # close iter call

  # Structural invariant maintained by the corofor producer (sem/hexer
  # genCall): `(haddr forLoopVar)` is the trailing arg, optionally
  # preceded by an env-arg when the target was pre-extracted. We
  # don't probe `lastArgPos.exprKind == HaddrX` — a regular iter arg
  # of `addr` shape would falsely match.
  let trailingCount = if upstreamEnvArg: 2 else: 1
  assert argCount >= trailingCount, "corofor: iter call missing args"
  let realArgCount = argCount - trailingCount

  # ---- emit `var it: Continuation = wrapper(args..., addr forLoopVar, callerCont)` ----
  # For iter-VALUE calls the callerCont's env is the iter value's
  # env-slot ref (so `caller.env != nil` → wrapper reuse branch).
  # For direct iter-sym calls the callerCont is the Stop sentinel
  # (`caller.env == nil` → wrapper fresh-frame branch).
  let itSym = pool.syms.getOrIncl("`coroIt." & $c.counter & "." & c.thisModuleSuffix)
  inc c.counter
  c.typeCache.registerLocal(itSym, VarY, default(Cursor))
  dest.copyIntoKind VarS, info:
    dest.addSymDef itSym, info
    dest.addDotToken() # exported
    dest.addDotToken() # pragmas
    dest.addSymUse pool.syms.getOrIncl(ContinuationName), info
    dest.copyIntoKind CallS, info:
      dest.add targetBuf
      var w = argsStart
      for i in 0 ..< realArgCount:
        dest.takeTree w
      var addrW = lastArgPos
      dest.takeTree addrW
      if upstreamEnvArg or valSymForEnv != SymId(0):
        # iter-value call: caller = `Continuation(fn: nil, env: addr(envSlot[]))`.
        # A bare `(cast (ptr CoroutineBase) ref)` would be a raw
        # bit-cast giving the ref-struct ptr (where the rc lives),
        # NOT the data ptr — so the wrapper would read garbage when
        # it accesses `caller.env.callee` etc. `(haddr (hderef ref))`
        # peels the ARC header and yields the underlying object's
        # address, which is the right shape for `ptr CoroutineBase`.
        dest.copyIntoKind OconstrX, info:
          dest.addSymUse pool.syms.getOrIncl(ContinuationName), info
          dest.copyIntoKind KvU, info:
            dest.addSymUse pool.syms.getOrIncl(FnFieldName), info
            dest.addParPair NilX, info
          dest.copyIntoKind KvU, info:
            dest.addSymUse pool.syms.getOrIncl(EnvFieldName), info
            dest.copyIntoKind CastX, info:
              dest.copyIntoKind PtrT, info:
                dest.addSymUse pool.syms.getOrIncl(coro_transform.RootObjName), info
              dest.copyIntoKind HaddrX, info:
                dest.copyIntoKind HderefX, info:
                  if upstreamEnvArg:
                    var envW = penultimateArgPos
                    dest.takeTree envW
                  else:
                    dest.copyIntoKind TupatX, valInfoForEnv:
                      dest.addSymUse valSymForEnv, valInfoForEnv
                      dest.addIntLit 1, valInfoForEnv
      else:
        coro_transform.emitStopContinuation(dest, info)

  # `myEnv` snapshot + try/while/finally — shared with cps's
  # `.passive` expansion via `coro_transform.emitWhileBegin`/
  # `emitWhileEnd`. The body walk uses `tre` (capture-rewriting), as
  # opposed to cps's `tr` (passive-state-machine emission); that's the
  # only behavioural difference between the two corofor expansions.
  let myEnvSym = pool.syms.getOrIncl("`coroEnv." & $c.counter & "." & c.thisModuleSuffix)
  inc c.counter
  c.typeCache.registerLocal(myEnvSym, LetY, default(Cursor))

  coro_transform.emitWhileBegin(dest, info, itSym, myEnvSym)
  while n.hasMore:
    treLoopBody(c, dest, n)
  coro_transform.emitWhileEnd(dest, info, itSym)

  skipParRi n # close (corofor

proc treSons(c: var Context; dest: var TokenBuf; n: var Cursor) =
  copyInto dest, n:
    while n.hasMore:
      tre(c, dest, n)

proc addEnvParam(dest: var TokenBuf; info: PackedLineInfo; envTyp: SymId) =
  dest.copyIntoKind ParamU, info:
    dest.addSymDef pool.syms.getOrIncl(EnvParamName), info
    dest.addDotToken() # no export marker
    dest.addDotToken() # no pragmas
    if envTyp == SymId(0):
      dest.copyIntoKind RefT, info:
        dest.addSymUse pool.syms.getOrIncl(BareRootObjName), info
    else:
      # to keep NIFC's type system happy we need a ptr type here
      # and then a cast in the body!
      dest.copyIntoKind PointerT, info: discard
    dest.addDotToken() # no default value

proc treParamsWithEnv(c: var Context; dest: var TokenBuf; n: var Cursor) =
  copyInto dest, n:
    while n.hasMore:
      tre(c, dest, n)
    addEnvParam dest, NoLineInfo, SymId(0)

proc treProcType(c: var Context; dest: var TokenBuf; n: var Cursor) =
  if itertypeNeedsTuple(n):
    # Closure / passive iterators get the wrapper-signature tuple shape
    # rather than the closure-proc shape. The wrapper signature lives in cps;
    # we mirror it here so the lifter sees the final tuple shape at
    # duplifier/destroyer time and hooks line up with cps's wrapper-proc
    # emission. `.closure` and `.passive` iters share the same tuple shape;
    # they differ only at the cps trampoline level.
    c.hasClosures = true
    emitIterTupleTypeFromParams(dest, n, n.info)
  elif isClosure(n):
    # type is really a tuple:
    let info = n.info
    copyIntoKind dest, TupleT, info:
      copyIntoKind dest, ProctypeT, info:
        dest.addDotToken() # nilability tag
        let inputKind = n.typeKind
        let isProctypeInput = inputKind == ProctypeT
        let usesWrapper = inputKind in RoutineTypes
        if usesWrapper:
          skipToParams n
        if n.substructureKind == ParamsU:
          treParamsWithEnv(c, dest, n)
        else:
          assert n.kind == DotToken
          inc n
          dest.addParLe ParamsU, info
          addEnvParam dest, info, SymId(0)
          dest.addParRi()
        tre c, dest, n # return type
        # pragmas:
        tre c, dest, n
        if usesWrapper and not isProctypeInput:
          # effects and body, deliberately made flexible here for future changes
          # as it's messy to work with.
          if n.hasMore:
            skip n
            if n.hasMore: skip n
        skipParRi n
      copyIntoKind dest, RefT, info:
        dest.addSymUse pool.syms.getOrIncl(BareRootObjName), info
  else:
    let isProctypeInput = n.typeKind == ProctypeT
    dest.takeToken n
    if isProctypeInput:
      # new layout: nilability, params, retType, pragmas
      for i in 0..3:
        if n.kind == ParRi: break
        tre c, dest, n
    else:
      # `proctype` is not the only routine TYPE with the short layout. A
      # `.passive` `itertype` reaches here too (`.closure` ones were taken by
      # `itertypeNeedsTuple` above) and has exactly the same four sons:
      # nilability, params, retType, pragmas. Only a routine DECLARATION has
      # `BodyPos` sons, and a declaration is what this branch exists for.
      # Without the `)` guard the four-son type ran the walk off its own end
      # into the enclosing tree and `tre` died on `bug "unexpected ')' inside"`
      # -- but only in a module that ALSO has a closure iter, because a module
      # with no closures never enters this walk at all, which is why the shape
      # survived unnoticed. A declaration never sees `)` early, so the guard
      # costs it nothing.
      for i in 0..<BodyPos:
        if n.kind == ParRi: break
        tre c, dest, n
      if n.hasMore:
        dest.takeTree n # don't transform the potential proc body here
    dest.takeParRi n

proc treType(c: var Context; dest: var TokenBuf; n: var Cursor)
  {.ensuresNif: addedType(dest).} =
  # Like `tre` but prefer the type interpretation. (Matters for ProcS etc.)
  if n.typeKind in RoutineTypes:
    treProcType(c, dest, n)
  else:
    tre(c, dest, n)

proc treLocal(c: var Context; dest: var TokenBuf; n: var Cursor) =
  let s = n.firstSon.symId
  let fld = c.envField(s)
  let kind = n.symKind
  if fld.field != SymId(0):
    # the local is already a field of an environment object
    let info = n.info
    let isResult = n.stmtKind == ResultS
    inc n # into the decl
    let name = n.symId
    for i in 1..3: skip n
    # register the local anyway to keep the type navigator happy:
    c.typeCache.registerLocal(name, kind, n)
    if isResult:
      # A captured `result` still needs a local for the `ret`, see `RetS` in `tre`.
      c.keptResults.incl name
      dest.copyIntoKind ResultS, info:
        dest.addSymDef name, info
        dest.addDotToken() # no export marker
        dest.addDotToken() # no pragmas
        var t = n
        treType c, dest, t
        dest.addDotToken() # no value
    skip n # type
    if n.kind == DotToken:
      # no value: `result` or `var x: T`. The slot starts out zeroed.
      inc n
    else:
      # generate an assignment:
      dest.copyIntoKind AsgnS, info:
        dest.copyIntoKind DotX, info:
          if c.env.needsHeap:
            dest.copyIntoKind DerefX, info:
              dest.typedEnv info, c.env
          else:
            dest.typedEnv info, c.env
          dest.addSymUse fld.field, info
        tre c, dest, n # value
    skipParRi n
  else:
    copyInto dest, n:
      let name = n.symId
      takeTree dest, n # name
      takeTree dest, n # export marker
      takeTree dest, n # pragmas
      c.typeCache.registerLocal(name, kind, n)
      let beforeType = dest.len
      treType c, dest, n # type (might grow an environment parameter)
      tre c, dest, n # value

proc treParams(c: var Context; dest, init: var TokenBuf; n: var Cursor; doAddEnvParam: bool; envTyp: SymId) =
  copyInto dest, n:
    while n.hasMore:
      assert n.substructureKind == ParamU
      copyInto dest, n:
        let name = n.symId
        takeTree dest, n # name
        takeTree dest, n # export marker
        takeTree dest, n # pragmas
        c.typeCache.registerLocal(name, ParamY, n)
        treType c, dest, n # type (might grow an environment parameter)
        tre c, dest, n # value

        # parameter might have been captured:
        let fld = c.envField(name)
        if fld.field != SymId(0):
          # XXX Check here for memory safety violations: Cannot capture a `var T` parameter
          # We're emitting `outer_env.<field> = <param>` into the
          # body-prologue (treProcBody splices `init` after the
          # env-local decl). `c.env` isn't usable yet — it'll be set
          # up by treProcBody AFTER this — so reference the env-local
          # by name (`EnvLocalName`) directly.
          #
          # `envTyp == SymId(0)` means "heap env" (the caller sets it
          # that way when the closureOwner escapes): the env-local is
          # `ref EnvT` and we need to deref before `.field`. For stack
          # env (`envTyp != 0`), the env-local IS the object and no
          # deref is needed. (The previous code had this inverted —
          # never tripped because the path was also broken by the
          # `typedEnv c.env` call with `c.env.s == 0`.)
          init.copyIntoKind AsgnS, n.info:
            init.copyIntoKind DotX, n.info:
              if envTyp == SymId(0):
                init.copyIntoKind DerefX, n.info:
                  init.addSymUse pool.syms.getOrIncl(EnvLocalName), n.info
              else:
                init.addSymUse pool.syms.getOrIncl(EnvLocalName), n.info
              init.addSymUse fld.field, n.info
            init.addSymUse name, n.info

    if doAddEnvParam:
      addEnvParam dest, n.info, envTyp

proc emitEnvLocal(c: var Context; dest: var TokenBuf; envTyp: SymId; needsHeap: bool; up: TokenBuf) =
  ## The local `c.env` names: the environment, with its link out set to `up`.
  dest.copyIntoKind VarS, NoLineInfo:
    dest.addSymDef c.env.s, NoLineInfo
    dest.addDotToken() # no export marker
    dest.addDotToken() # no pragmas
    if needsHeap:
      dest.copyIntoKind RefT, NoLineInfo:
        dest.addSymUse c.env.typ, NoLineInfo
      dest.copyIntoKind NewobjX, NoLineInfo:
        dest.copyIntoKind RefT, NoLineInfo:
          dest.addSymUse c.env.typ, NoLineInfo
    else:
      dest.addSymUse c.env.typ, NoLineInfo
      dest.addDotToken() # no default value
  if needsHeap:
    # Note: If the environment is on the stack, a single `wasMoved`
    # hook will be generated for it so we don't need to do anything here.
    # Otherwise, we need to init the environment via the `=wasMoved` hooks:
    for _, field in c.localToEnv:
      # A view (a `for` variable over a seq, say) is a pointer, with no hook.
      if field.objType == c.env.typ and field.typ.typeKind notin {LentT, MutT, OutT}:
        dest.copyIntoKind WasmovedX, NoLineInfo:
          dest.copyIntoKind HaddrX, NoLineInfo:
            dest.copyIntoKind DotX, NoLineInfo:
              if needsHeap:
                dest.copyIntoKind DerefX, NoLineInfo:
                  dest.addSymUse c.env.s, NoLineInfo
              else:
                dest.addSymUse c.env.s, NoLineInfo
              dest.addSymUse field.field, NoLineInfo
    if c.envUp.getOrDefault(envTyp) != SymId(0):
      dest.copyIntoKind WasmovedX, NoLineInfo:
        dest.copyIntoKind HaddrX, NoLineInfo:
          dest.copyIntoKind DotX, NoLineInfo:
            dest.copyIntoKind DerefX, NoLineInfo:
              dest.addSymUse c.env.s, NoLineInfo
            dest.addSymUse c.envUp.getOrDefault(envTyp), NoLineInfo
  # Keep the environment this routine was given: the routines nested in
  # this one reach the enclosing routines' locals through it.
  if c.envUp.getOrDefault(envTyp) != SymId(0):
    dest.copyIntoKind AsgnS, NoLineInfo:
      dest.copyIntoKind DotX, NoLineInfo:
        if needsHeap:
          dest.copyIntoKind DerefX, NoLineInfo:
            dest.addSymUse c.env.s, NoLineInfo
        else:
          dest.addSymUse c.env.s, NoLineInfo
        dest.addSymUse c.envUp.getOrDefault(envTyp), NoLineInfo
      dest.copyTree up

proc treProcBody(c: var Context; dest, init: var TokenBuf; n: var Cursor; sym: SymId; needsHeap: bool) =
  if n.stmtKind == StmtsS:
    copyInto dest, n:
      let oldEnv = c.env
      if c.createsEnv.contains(sym):
        let envTyp = c.envTypeForProc(sym)
        c.env = CurrentEnv(s: pool.syms.getOrIncl(EnvLocalName), mode: EnvIsLocal, typ: envTyp, needsHeap: needsHeap)
        var up = createTokenBuf(1)
        up.addSymUse pool.syms.getOrIncl(EnvParamName), NoLineInfo
        emitEnvLocal c, dest, envTyp, needsHeap, up
      elif c.closureProcs.contains(sym):
        c.env = CurrentEnv(s: pool.syms.getOrIncl(EnvParamName), mode: EnvIsParam, typ: c.envTypeForProc(sym), needsHeap: needsHeap)
      else:
        c.env = CurrentEnv(s: SymId(0), mode: EnvIsParam, typ: SymId(0), needsHeap: needsHeap)
      dest.add init
      while n.hasMore:
        tre(c, dest, n)
      var needsHeapB = c.env.needsHeap
      c.env = oldEnv
      c.env.needsHeap = c.env.needsHeap or needsHeapB
  else:
    tre(c, dest, n)

proc treLoopBody(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## Pass 2 of a loop's body, see `trWhile`. The environment of a loop scope is made
  ## as the body is entered, and a closure made in the body takes that one.
  if n.stmtKind == BlockS and n.firstSon.kind in {SymbolDef, DotToken}:
    var inner = n.firstSon
    skip inner
    if inner.stmtKind == StmtsS and inner.firstSon.stmtKind == CommentS:
      dest.takeToken n # block
      dest.takeTree n # label
      treLoopBody c, dest, n
      dest.takeParRi n
      return
  var scope = SymId(0)
  if n.stmtKind == StmtsS:
    let first = n.firstSon
    if first.stmtKind == CommentS:
      var m = first
      inc m
      if m.kind == Symbol and c.loopScopes.contains(m.symId):
        scope = m.symId
  if scope == SymId(0):
    tre c, dest, n
  else:
    dest.add n
    inc n
    skip n # the marker
    let oldEnv = c.env
    let info = n.info
    c.procStack.add scope
    if c.createsEnv.contains(scope):
      let envTyp = c.envTypeForProc(scope)
      let holder = pool.syms.getOrIncl("`el." & $(c.counter + 1))
      inc c.counter
      c.loopEnvLocal[scope] = holder
      var up = createTokenBuf(4)
      if oldEnv.s == SymId(0):
        up.addParPair NilX, info
      else:
        untypedEnv up, info, oldEnv,
          (if not oldEnv.needsHeap and oldEnv.mode == EnvIsLocal: WantAddr else: WantValue)
      c.env = CurrentEnv(s: holder, mode: EnvIsLocal, typ: envTyp, needsHeap: oldEnv.needsHeap)
      emitEnvLocal c, dest, envTyp, oldEnv.needsHeap, up
    while n.hasMore:
      tre c, dest, n
    c.env = oldEnv
    discard c.procStack.pop()
    dest.takeParRi n

proc treWhile(c: var Context; dest: var TokenBuf; n: var Cursor) =
  copyInto dest, n:
    tre c, dest, n # condition, or the iterator's call
    while n.hasMore:
      treLoopBody c, dest, n

proc signatureMentionsClosure(decl: Cursor): bool =
  ## Does this routine's PARAMS or RETURN TYPE mention a `.closure` routine
  ## type? Those are exactly the signatures whose shape pass 2 rewrites.
  var n = decl
  if n.kind != ParLe: return false
  inc n
  for i in 0..<ParamsPos: skip n
  if mentionsClosureRoutineType(n): return true
  skip n
  result = mentionsClosureRoutineType(n)

proc treProc(c: var Context; dest: var TokenBuf; n: var Cursor) =
  var init = createTokenBuf(10)
  let decl = n
  # Pass 2 rewrites a `.closure` routine type in a signature to its `(fn, env)`
  # tuple, but it never told the symbol table. Every LATER pass resolves a
  # routine through `tryLoadSym`, so they all kept reading the PRE-lowering
  # signature, and a temp typed from it got the bare proctype while the callee
  # it was initialised from returned the tuple:
  #
  #   var fs: seq[proc (x: int): int {.closure.}] = @[]
  #   fs.add proc (x: int): int {.closure.} = x + 1
  #   echo fs[0](2)
  #
  # Here `seq.[]` is instantiated at the closure type, so its return type
  # genuinely changes shape. xelim hoisted the `fs[0]` result into a temp whose
  # declared type it read from the stale signature, and the C did not compile:
  #   error: initialization of 'NI64 (**)(NI64)' from incompatible pointer type
  # Republishing keeps the two in step. Only signatures that actually mention a
  # closure routine type are republished, so this cannot disturb any routine
  # whose shape pass 2 leaves alone.
  let republishSig = signatureMentionsClosure(decl)
  let declStart = dest.len
  var procSym = SymId(0)
  copyInto dest, n:
    var isConcrete = true # assume it is concrete
    let sym = n.symId
    procSym = sym
    c.procStack.add(sym)
    let closureOwner = c.procStack[0]
    let needsHeap = c.escapes.contains(closureOwner)
    for i in 0..<BodyPos:
      if i == ParamsPos:
        c.typeCache.openProcScope(sym, decl, n)
        let envType = if needsHeap: SymId(0) else: c.envTypeForProc(closureOwner)
        treParams c, dest, init, n, c.closureProcs.contains(sym), envType
      else:
        if i == TypevarsPos:
          isConcrete = n.substructureKind != TypevarsU
        if i == ReturnTypePos and isConcrete:
          treType c, dest, n
        else:
          takeTree dest, n

    if republishSig and procSym != SymId(0):
      # Everything up to (not including) the body is the signature. Mirrors
      # `programs.publishSignature`, which cannot be used directly because it
      # publishes to the END of `dest` and the body has not been written yet.
      var sigBuf = createTokenBuf(dest.len - declStart + 3)
      for i in declStart..<dest.len: sigBuf.add dest[i]
      sigBuf.addDotToken() # body is empty for a signature
      sigBuf.addParRi()
      programs.publish(procSym, sigBuf, SemcheckSignatures)

    if isConcrete:
      treProcBody(c, dest, init, n, sym, needsHeap)
    else:
      takeTree dest, n
    discard c.procStack.pop()
  c.typeCache.closeScope()

proc treProcLift(c: var Context; dest: var TokenBuf; n: var Cursor) =
  # `genCall` walks the arguments of a closure call twice, for the call with an
  # environment and the one without: a lambda among them is one routine still.
  if c.liftedProcs.containsOrIncl(n.firstSon.symId):
    skip n
    return
  if c.procStack.len == 0:
    swap c.dest, dest
  var lift = createTokenBuf(16)
  treProc c, lift, n
  c.dest.add lift
  if c.procStack.len == 0:
    swap c.dest, dest

proc isStaticCall(c: var Context;s: SymId): bool =
  let res = tryLoadSym(s)
  if res.status == LacksNothing:
    let fn = asRoutine(res.decl)
    result = isRoutine(fn.kind)
  else:
    let local = c.typeCache.getLocalInfo(s)
    result = isRoutine(local.kind)

proc toNonClosureProcType(c: var Context; dest: var TokenBuf; n: Cursor) =
  # The type of the routine without the closure pragma, and without the environment
  # parameter when an alias already took the type to its lowered `(fn, env)` shape.
  # Always the short form: a lambda's type is its declaration, whose body names
  # locals that are out of scope in the caller.
  var n = n
  let lifted = isLiftedClosureTuple(n)
  if lifted: inc n
  assert n.typeKind in RoutineTypes
  let info = n.info
  dest.copyIntoKind ProctypeT, info:
    dest.addDotToken() # nilability tag
    skipToParams n
    dest.copyIntoKind ParamsU, n.info:
      if n.kind == DotToken:
        inc n
      else:
        n.into:
          while n.hasMore:
            var after = n
            skip after
            if lifted and after.kind == ParRi:
              skip n
            else:
              tre c, dest, n
    tre c, dest, n # return type
    if n.kind == DotToken:
      dest.addDotToken()
    else:
      dest.copyIntoKind PragmasU, n.info:
        var p = n
        inc p
        while p.hasMore:
          if p.pragmaKind == ClosureP:
            skip p
          else:
            takeTree dest, p

proc containsEnvp(n: Cursor): bool =
  var nested = 0
  var n = n
  while true:
    case n.kind
    of ParLe:
      if n.exprKind == EnvpX: return true
      inc n
      inc nested
    of ParRi:
      inc n
      dec nested
    else:
      inc n
    if nested == 0: break
  false

proc copyEnvpTypable(dest: var TokenBuf; n: var Cursor) =
  ## Copies `n` with its `(envp T fld)` spelled so the type navigator can follow
  ## it: it answers `auto` for `envp`, and a call through a captured object,
  ## `inner.enc(a)`, was then not seen to be a call of a closure at all.
  if n.kind == ParLe and n.exprKind == EnvpX:
    let info = n.info
    inc n
    dest.copyIntoKind DotX, info:
      dest.copyIntoKind DerefX, info:
        dest.copyIntoKind CastX, info:
          dest.copyIntoKind RefT, info:
            dest.takeTree n
          dest.addParPair NilX, info
      dest.takeTree n
    skipParRi n
  elif n.kind == ParLe:
    dest.takeToken n
    while n.kind != ParRi:
      copyEnvpTypable dest, n
    dest.takeToken n
  else:
    dest.takeToken n

proc typeOfCallee(c: var Context; n: Cursor; holder: var TokenBuf): Cursor =
  if containsEnvp(n):
    var m = n
    copyEnvpTypable holder, m
    result = c.typeCache.getType(beginRead(holder), {SkipAliases})
  else:
    result = c.typeCache.getType(n, {SkipAliases})

proc genCall(c: var Context; dest: var TokenBuf; n: var Cursor) =
  let info = n.info
  let callNode = n  # the call node itself
  inc n
  let fn = n
  var calleeHolder = createTokenBuf(8)
  let typ = typeOfCallee(c, n, calleeHolder)
  # A closure iter-value call target type can appear here in two guises:
  #   - raw `(itertype … (pragmas (closure)))` — `isClosure` matches.
  #   - lifted `(tuple <proctype> (ref RootObj))` — `isLiftedClosureTuple`
  #     matches (when getType already follows the alias to the rewritten
  #     body). `.passive` iter values are NOT iter-value tuples; cps's
  #     `trProctype` lowers them to plain function pointers, and they
  #     reach genCall as ordinary proctype calls — not wrapped.
  #
  # Iter SYM in static call position (`countup(1, 5)` inside a corofor)
  # is NOT a closure-value call — coro_transform.trCoroFor rewrites
  # this to a wrapper-proc call with explicit `StopContinuation`. We
  # must not append an env-arg here, otherwise the trampoline expects
  # the env-arg to be the addr-of-result and bails.
  let wantsEnv = isClosure(typ) or isLiftedClosureTuple(typ) or
                 (n.kind == Symbol and c.closureProcs.contains(n.symId))
  var isStatic = false
  var tmp = SymId(0)
  var needNilCheck = false
  if wantsEnv:
    isStatic = n.kind == Symbol and isStaticCall(c, n.symId)
    if isStatic:
      dest.add callNode
      # do not produce a tuple:
      dest.add n
      inc n
    elif n.kind == Symbol:
      tmp = n.symId
      needNilCheck = true
      dest.addParLe IfS, info
      dest.addParLe ElifU, info
      # env == nil means calls the non closure procedure that was converted to a closure procedure
      copyIntoKind dest, NeqX, info:
        if c.env.needsHeap:
          dest.addRootRef info
        else:
          dest.copyIntoKind PointerT, info: discard
        copyIntoKind dest, TupatX, info:
          dest.addSymUse tmp, info
          dest.addIntLit 1, info
        dest.addParPair NilX, info
      dest.add callNode
      copyIntoKind dest, TupatX, info:
        #tre c, dest, n
        takeToken dest, n
        dest.addIntLit 0, info
    else:
      dest.add callNode
      dest.addParLe(ExprX, info)
      copyIntoKind dest, StmtsS, info:
        tmp = pool.syms.getOrIncl("`llTemp." & $c.counter)
        inc c.counter
        copyIntoKind dest, VarS, info:
          dest.addSymDef tmp, info
          dest.addDotToken() # no export marker
          dest.addDotToken() # no pragmas
          var t = typ
          tre c, dest, t
          tre c, dest, n # value
      # The callee slot takes the FUNCTION half of the closure pair, not the
      # pair. The `n.kind == Symbol` branch above spells that `(tupat sym 0)`;
      # this branch (a non-symbol callee -- `h.cb(1)`, an object field holding a
      # closure) hoisted the pair into `llTemp` and then handed `llTemp` itself
      # to `(call ...)`, so the call's function operand had tuple type while its
      # trailing env argument was correctly `(tupat llTemp 1)`. Nothing further
      # down the pipeline can repair that: eraiser is the first pass to ask for
      # the callee's params and dies on `fnType.tagEnum == ParamsTagId`.
      dest.copyIntoKind TupatX, info:
        dest.addSymUse tmp, info
        dest.addIntLit 0, info
      dest.addParRi() # ExprX
  else:
    dest.add callNode
  while n.hasMore:
    tre(c, dest, n)
  if wantsEnv:
    if isStatic:
      # Null for toplevel closures that have been declared .closure for interop.
      emitEnvFor c, dest, info, fn.symId
    else:
      # unpack the tuple:
      assert tmp != SymId(0)
      copyIntoKind dest, TupatX, info:
        dest.addSymUse tmp, info
        dest.addIntLit 1, info
  dest.addParRi()
  skipParRi n

  if needNilCheck:
    dest.addParRi() # end of ElifU
    copyIntoKind dest, ElseU, info:
      dest.add callNode
      var n2 = fn
      copyIntoKind dest, CastX, info:
        c.toNonClosureProcType dest, typ
        copyIntoKind dest, TupatX, info:
          takeToken dest, n2
          dest.addIntLit 0, info
      while n2.hasMore:
        tre(c, dest, n2)
      dest.addParRi() # end of call
    dest.addParRi() # end of IfS

proc toProcType(c: var Context; dest: var TokenBuf; n: Cursor) =
  var n = n
  let info = n.info
  copyIntoKind dest, ProctypeT, info:
    dest.addDotToken() # nilability tag
    skipToParams n
    copyIntoKind dest, ParamsU, n.info:
      if n.kind == DotToken:
        inc n
      else:
        n.into:
          while n.hasMore:
            tre c, dest, n # params
      addEnvParam dest, info, SymId(0)
    tre c, dest, n # return type
    # pragmas:
    tre c, dest, n
    while n.hasMore: skip n
    skipParRi n

proc treKv(c: var Context; dest: var TokenBuf; n: var Cursor) =
  copyInto dest, n:
    dest.takeTree n # key
    while n.hasMore:
      tre(c, dest, n)

proc treTupleType(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## The sons of a tuple type are types, and the type of a lambda is spelled as the
  ## lambda's whole declaration: to `tre` it would be that declaration again, lifted
  ## once more or lost.
  copyInto dest, n:
    while n.hasMore:
      if n.substructureKind == KvU:
        copyInto dest, n:
          takeTree dest, n # name
          treType c, dest, n
      else:
        treType c, dest, n

proc treToClosure(c: var Context; dest: var TokenBuf; n: var Cursor) =
  let info = n.info
  let origTyp = c.typeCache.getType(n, {SkipAliases})
  inc n
  dest.copyIntoKind TupconstrX, info:
    dest.copyIntoKind TupleT, info:
      c.toProcType(dest, origTyp)
      dest.addRootRef info
    dest.copyIntoKind CastX, info:
      c.toProcType(dest, origTyp)
      tr c, dest, n
    dest.addParPair NilX, info
  skipParRi n

proc lowerTypeDecl(c: var Context; dest: var TokenBuf; n: var Cursor): SymId =
  result = SymId(0)
  dest.takeToken n              # `type` tag
  if n.kind == SymbolDef: result = n.symId
  for i in 0..3: takeTree dest, n   # name, exported, typevars, pragmas
  if n.hasMore:
    treType c, dest, n          # the body -- the part that needs lowering
  while n.hasMore: takeTree dest, n
  dest.takeParRi n

proc treTypeDecl(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## A type DECLARATION was taken verbatim by pass 2, but pass 2 is exactly the
  ## pass that rewrites a `.closure` routine type to its `(fn, env)` tuple. So a
  ## closure proc reached through a type declaration -- an object field, a tuple
  ## field, a plain alias -- kept the bare proctype while every USE of it became
  ## the two-word tuple:
  ##
  ##   type Holder = object
  ##     cb: proc (x: int): int {.closure.}
  ##   var h = Holder(cb: proc (x: int): int {.closure.} = x * k)
  ##   echo h.cb(4)
  ##
  ## emitted `Holder.cb` as a plain `NI64 (*)(NI64)` and then initialised that
  ## field from the tuple, so the generated C did not compile:
  ##   error: incompatible types when initializing type 'NI64 (*)(NI64)'
  ##          using type '<closure tuple>'
  ## A LOCAL of the very same type was always lowered (`treLocal` -> `treType`),
  ## which is why only the field/alias spelling was broken and a closure held in
  ## a `var` never showed it.
  ##
  ## Declarations that mention no closure routine type are still taken verbatim,
  ## so this cannot perturb the emitted tree for any module it does not concern.
  if not mentionsClosureRoutineType(n):
    takeTree dest, n
    return
  let typeStart = dest.len
  let typeSym = lowerTypeDecl(c, dest, n)
  if typeSym != SymId(0):
    # Downstream (lifter, lengcgen) resolves the field types through the symbol
    # table, not through this buffer, so the rewritten shape has to be published
    # or they would still see the un-lowered proctype.
    programs.publish(typeSym, dest, typeStart)

proc tre(c: var Context; dest: var TokenBuf; n: var Cursor) =
  case n.kind
  of Symbol:
    # is this the usage of a proc symbol that is a closure? If so,
    # turn it into a `(fn, env)` tuple and generate the environment.
    let origTyp = c.typeCache.getType(n, {SkipAliases})
    let info = n.info
    if isClosureIterSym(n.symId):
      # Closure iter sym used as a VALUE — emit the wrapper-shape
      # iter-value tuple. Lambdalifting OWNS `.closure` iter
      # transformation (state machine + wrapper generated in
      # `transformClosureIter`), so the iter sym refers to the
      # state-machine entry (5 params: a, b, this, result, caller),
      # NOT a callable matching the tuple's declared type. The
      # WRAPPER sym (`iter.init.<mod>`) matches the declared 4-param
      # wrapper proctype; emit that directly.
      #
      # Pre-publish a placeholder signature for the wrapper so
      # downstream passes (eraiser / duplifier / destroyer) can
      # resolve its type before cps would have generated it.
      #
      # Env slot: eagerly allocate `(newobj (ref CoroType))` so the
      # iter VALUE owns its frame. Each evaluation of an iter-sym at
      # a value position creates an independent frame. The wrapper's
      # `caller.env != nil` reuse branch detects on first call (via
      # `this.callee == nil`) that this is a fresh frame and inits
      # it; subsequent calls dispatch via the resume slot
      # (`caller.fn`). This is Nim's shared-state semantics:
      # `let g = countup(1, 5); for x in g(): if x == 3: break; for x
      # in g(): echo x` resumes at 4 instead of restarting at 1.
      # The frame is wrapped in `(cast (ref RootObj) …)` because the
      # tuple slot's declared type is `(ref RootObj)` — Nim's real
      # `RootObj`, the base of the `CoroutineBase` hierarchy
      # `CoroType` inherits from.
      #
      # Important: this MUST come before the generic closure-proc
      # branch because iter decls match `RoutineKinds`/`isClosure`
      # too, but the env-injection path below would feed them the
      # wrong shape.
      let iterSym = n.symId
      coro_transform.publishWrapperSignature(iterSym, c.thisModuleSuffix)
      dest.copyIntoKind TupconstrX, info:
        emitIterTupleTypeFromSym(dest, iterSym, info)
        dest.addSymUse coro_transform.coroWrapperForExternIter(iterSym), info
        dest.copyIntoKind CastX, info:
          dest.copyIntoKind RefT, info:
            dest.addSymUse pool.syms.getOrIncl(BareRootObjName), info
          dest.copyIntoKind NewobjX, info:
            dest.copyIntoKind RefT, info:
              dest.addSymUse coro_transform.coroTypeForExternIter(iterSym), info
      inc n
    elif origTyp.typeKind in RoutineTypes and isClosure(origTyp) and c.typeCache.fetchSymKind(n.symId) in RoutineKinds:
      dest.copyIntoKind TupconstrX, info:
        dest.copyIntoKind TupleT, info:
          c.toProcType(dest, origTyp)
          dest.addRootRef info
        dest.addSymUse n.symId, info
        # A `.closure` lambda that captures NOTHING has no environment: the pair
        # still needs its second son, a null env, exactly what `trNil` writes for
        # a nil closure.
        emitEnvFor c, dest, info, n.symId
      inc n
    else:
      if emitLocalSlot(c, dest, n.symId, info):
        inc n
      else:
        takeTree dest, n
  of DotToken, UnknownToken, EofToken, Ident, SymbolDef,
     IntLit, UIntLit, FloatLit, CharLit, StringLit:
    takeTree dest, n
  of ParLe:
    case n.stmtKind
    of LocalDecls:
      treLocal c, dest, n
    of ProcS, FuncS, MethodS, ConverterS:
      if n.firstSon.kind == DotToken: # no name: a type, not a declaration
        treProcType c, dest, n
      else:
        treProcLift c, dest, n
    of IteratorS:
      # `.closure` iter decls: run the coro-transform pipeline here
      # so the state machine + frame type + wrapper are emitted at
      # lambdalifting time. The decl is retagged ProcS in the
      # process, so cps's `(IteratorY and ClosureP)` gate no longer
      # fires on it. `.passive` iter decls pass through to cps as
      # before.
      if isClosureIterDecl(n):
        transformClosureIter c, dest, n
      else:
        takeTree dest, n
    of TypeS:
      treTypeDecl c, dest, n
    of RetS:
      # Returning the slot directly would read it after the routine's scope ended
      # and dropped the environment: the value goes to a real local first.
      var value = n
      inc value
      if value.kind == Symbol and c.keptResults.contains(value.symId):
        let info = n.info
        let name = value.symId
        dest.copyIntoKind StmtsS, info:
          dest.copyIntoKind AsgnS, info:
            dest.addSymUse name, info
            discard emitLocalSlot(c, dest, name, info)
          dest.copyIntoKind RetS, info:
            dest.addSymUse name, info
        skip n
      else:
        treSons c, dest, n
    of MacroS, TemplateS, EmitS, BreakS, ContinueS,
      ForS, IncludeS, ImportS, FromimportS, ImportexceptS,
      ExportS, CommentS,
      PragmasS:
      takeTree dest, n
    of ScopeS:
      c.typeCache.openScope()
      treSons(c, dest, n)
      c.typeCache.closeScope()
    of CoroforS:
      # `.closure` iter corofors are owned by lambdalifting — we expand
      # them into the trampoline here so the body walk goes through
      # `tre` (capture rewriting). `.passive` iter corofors pass
      # through to cps's `coro_transform.trCoroFor`.
      if isClosureCoroFor(c, n):
        trClosureCoroFor c, dest, n
      else:
        treWhile c, dest, n
    of WhileS:
      treWhile c, dest, n
    of CallS, CmdS, BlockS, AsgnS, IfS, WhenS,
      CaseS, YldS, StmtsS, PragmaxS, InclS, ExclS, ImportasS,
      ExportexceptS, DiscardS, TryS, RaiseS, UnpackdeclS,
      AssumeS, AssertS, CallstrlitS, InfixS, PrefixS, HcallS,
      StaticstmtS, BindS, MixinS, UsingS, AsmS, DeferS,
      NoStmt:
      case n.exprKind
      of CallKinds:
        genCall(c, dest, n)
      of DotX:
        takeToken dest, n
        tre c, dest, n
        takeTree dest, n # don't look up field names here
        if n.hasMore: takeTree dest, n # optional inheritance depth
        if n.hasMore: takeTree dest, n # optional access-token string lit
        takeParRi dest, n
      of CastX, ConvX:
        takeToken dest, n
        treType c, dest, n
        while n.hasMore:
          tre c, dest, n
        takeParRi dest, n
      of HconvX:
        # `c != nil` is the pointer comparison, of `(hconv pointer c)`. A closure is
        # two words: what tells whether it is nil is its function.
        var operand = n
        inc operand
        let wantsPointer = operand.typeKind == PointerT
        skip operand
        var holder = createTokenBuf(8)
        var isClosureValue = false
        if wantsPointer:
          let t = typeOfCallee(c, operand, holder)
          isClosureValue = isClosure(t) or isLiftedClosureTuple(t)
        if isClosureValue:
          let info = n.info
          dest.takeToken n
          treType c, dest, n
          dest.copyIntoKind TupatX, info:
            tre c, dest, n
            dest.addIntLit 0, info
          dest.takeParRi n
        else:
          treSons c, dest, n
      of EnvpX:
        let info = n.info
        inc n
        let owner = envOwnerIndex(c, n.symId)
        assert owner >= 0
        dest.copyIntoKind DotX, info:
          dest.copyIntoKind DerefX, info:
            dest.copyIntoKind CastX, info:
              dest.copyIntoKind (if c.env.needsHeap: RefT else: PtrT), info:
                dest.takeTree n # type
              # The local may belong to a routine further out than the one whose
              # environment this routine holds: follow the links out to it.
              emitChildEnv c, dest, info, owner
          assert n.kind == Symbol
          dest.takeTree n # the symbol
        skipParRi n
      of TypeofX:
        takeTree dest, n
      of ToClosureX:
        treToClosure c, dest, n
      of ErrX, SufX, AtX, DerefX, PatX, ParX, AddrX, NilX,
        InfX, NeginfX, NanX, FalseX, TrueX, AndX, OrX, XorX,
        NotX, NegX, SizeofX, AlignofX, OffsetofX, OconstrX,
        AconstrX, BracketX, CurlyX, CurlyatX, OvfX, AddX,
        SubX, MulX, DivX, ModX, ShrX, ShlX, BitandX, BitorX,
        BitxorX, BitnotX, EqX, NeqX, LeX, LtX, CchoiceX,
        OchoiceX, PragmaxX, QuotedX, HderefX, DdotX, HaddrX,
        NewrefX, NewobjX, TupX, TupconstrX, SetconstrX,
        TabconstrX, AshrX, BaseobjX, DconvX,
        CompilesX, DeclaredX, DefinedX, AstToStrX, BindSymX, BindSymNameX, InstanceofX,
        HighX, LowX, UnpackX, FieldsX, FieldpairsX,
        EnumtostrX, IsmainmoduleX, DefaultobjX, DefaulttupX,
        DefaultdistinctX, Delay0X, SuspendX, ExprX, DoX,
        ArratX, TupatX, PlussetX, MinussetX, MulsetX, XorsetX,
        EqsetX, LesetX, LtsetX, InsetX, CardX, EmoveX,
        DestroyX, DupX, CopyX, WasmovedX, SinkhX, TraceX,
        InternalTypeNameX, InternalFieldPairsX, FailedX, IsX,
        KvX, NoExpr:
        if n.typeKind == TupleT and isLiftedClosureTuple(n):
          # An iter-value tuple or closure-proc tuple emitted by an earlier
          # pass — don't recurse into it, otherwise treProcType would fire
          # again on the inner ProctypeT and wrap it in ANOTHER tuple. The
          # shape is stable already; take it verbatim.
          takeTree dest, n
        elif n.typeKind in RoutineTypes:
          treProcType(c, dest, n)
        elif n.typeKind == TupleT:
          treTupleType(c, dest, n)
        elif n.substructureKind == KvU:
          treKv(c, dest, n)
        else:
          treSons(c, dest, n)
  of ParRi:
    bug "unexpected ')' inside"

proc genObjectTypes(c: var Context; dest: var TokenBuf) =
  ## Every routine with captured locals has its own environment. A nested one that
  ## also reaches further out keeps a link to the environment it was handed, as a
  ## routine has just the one parameter for an environment:
  ##
  ##   proc main() =          # env: a
  ##     var a = 1
  ##     let f = proc () =    # env: b, up (main's env)
  ##       var b = 2
  ##       let g = proc () =  # no env; its env parameter is f's env
  ##         use a, b
  var objectTypes = initTable[SymId, seq[EnvField]]()
  for local, field in c.localToEnv:
    objectTypes.mgetOrPut(field.objType, @[]).add(field)
  for owner in items c.createsEnv:
    if c.capturers.contains(owner) and c.procParent.hasKey(owner):
      let name = "`up." & $c.counter & "." & c.thisModuleSuffix
      inc c.counter
      c.envUp[c.envTypeForProc(owner)] = pool.syms.getOrIncl(name)
  for objType, fields in objectTypes:
    let beforeType = dest.len
    dest.copyIntoKind TypeS, NoLineInfo:
      dest.addSymDef objType, NoLineInfo
      dest.addDotToken() # no export marker
      dest.addDotToken() # no generic params
      dest.addDotToken() # no pragmas
      dest.copyIntoKind ObjectT, NoLineInfo:
        # inherits from RootObj:
        dest.addSymUse pool.syms.getOrIncl(BareRootObjName), NoLineInfo
        for field in items fields:
          let beforeField = dest.len
          dest.copyIntoKind FldY, NoLineInfo:
            dest.addSymDef field.field, NoLineInfo
            dest.addDotToken() # no export marker
            dest.addDotToken() # no pragmas
            var n = field.typ
            # type might need an environment parameter; and it is a TYPE, though
            # the type of a lambda is spelled as the lambda's whole declaration.
            treType(c, dest, n)
            dest.addDotToken() # no default value
          programs.publish(field.field, dest, beforeField)
        let up = c.envUp.getOrDefault(objType)
        if up != SymId(0):
          let beforeField = dest.len
          dest.copyIntoKind FldY, NoLineInfo:
            dest.addSymDef up, NoLineInfo
            dest.addDotToken() # no export marker
            dest.addDotToken() # no pragmas
            # Owning when the nest's environments live on the heap, like the
            # environment slot of a closure value.
            var heap = false
            for owner in items c.createsEnv:
              if c.envTypeForProc(owner) == objType:
                var root = owner
                while c.procParent.hasKey(root):
                  root = c.procParent.getOrDefault(root)
                heap = c.escapes.contains(root)
            if heap:
              dest.addRootRef NoLineInfo
            else:
              dest.copyIntoKind PointerT, NoLineInfo: discard
            dest.addDotToken() # no default value
          programs.publish(up, dest, beforeField)
    programs.publish(objType, dest, beforeType)

proc propagateCapturers(c: var Context) =
  ## Using a nested routine takes the environment it runs on: the user has to have
  ## it even when it captures nothing itself, and the routines in between have to
  ## pass it along.
  var changed = true
  while changed:
    changed = false
    for r in items c.procRefs:
      if c.capturers.contains(r[1]) and c.procParent.hasKey(r[1]):
        let parent = c.procParent.getOrDefault(r[1])
        var cur = r[0]
        while cur != parent and cur != SymId(0):
          if not c.capturers.contains(cur):
            c.capturers.incl cur
            c.closureProcs.incl cur
            changed = true
          cur = c.procParent.getOrDefault(cur)

var retiredDecls: seq[TokenBuf] = @[]
  ## Replaced declarations of other modules: a later stage of this process can
  ## still hold a cursor into one.

proc lowerForeignDecl(c: var Context; s: SymId; n: Cursor) =
  ## The declaration of a symbol of another module is what that module's frontend
  ## wrote: read from there, a closure routine type still is a bare proctype, while
  ## every use is the two-word `(fn, env)` tuple. The lifter called such a field
  ## trivial, so a closure stored in an imported object took no reference on its
  ## environment, and one hoisted out of it for a call had a destroy but no dup.
  ## Give this process the lowered declaration, as this pass does for the module's
  ## own ones.
  var buf = createTokenBuf(40)
  var n = n
  if n.stmtKind == TypeS:
    discard lowerTypeDecl(c, buf, n)
  elif n.stmtKind in LocalDecls:
    copyInto buf, n:
      for i in 0..2: takeTree buf, n # name, exported, pragmas
      treType c, buf, n
      while n.hasMore: takeTree buf, n
  else:
    copyInto buf, n:
      for i in 0..<ParamsPos: takeTree buf, n
      copyInto buf, n:
        while n.hasMore:
          copyInto buf, n:
            for i in 0..2: takeTree buf, n # name, exported, pragmas
            treType c, buf, n
            while n.hasMore: takeTree buf, n
      treType c, buf, n # return type
      while n.hasMore: takeTree buf, n
  let entry = getEntry(s)
  if entry != nil:
    retiredDecls.add move(entry.buffer)
  programs.publish(s, buf, 0)

proc isGenericDecl(n: Cursor): bool =
  if n.stmtKind == TypeS: asTypeDecl(n).isGeneric
  else: asRoutine(n).isGeneric

proc sweepClosures(c: var Context; n: Cursor; found: var bool)

proc sweepForeignSym(c: var Context; s: SymId; found: var bool) =
  if c.sweepSeen.containsOrIncl(s): return
  let name = pool.syms[s]
  let modname = extractModule(name)
  if modname.len == 0 or modname == c.thisModuleSuffix: return
  let res = tryLoadSym(s)
  if res.status != LacksNothing: return
  let decl = res.decl
  var lower = false
  case decl.stmtKind
  of TypeS:
    let t = asTypeDecl(decl)
    if t.isGeneric: return
    sweepClosures c, t.body, found
    lower = mentionsClosureRoutineType(t.body)
  of ProcS, FuncS, MethodS, ConverterS:
    let r = asRoutine(decl)
    if r.isGeneric: return
    sweepClosures c, r.params, found
    sweepClosures c, r.retType, found
    lower = signatureMentionsClosure(decl)
  of LocalDecls:
    let l = asLocal(decl)
    sweepClosures c, l.typ, found
    lower = mentionsClosureRoutineType(l.typ)
  else:
    return
  if lower:
    lowerForeignDecl c, s, decl

proc sweepClosures(c: var Context; n: Cursor; found: var bool) =
  ## Does this tree reach a closure routine type, through other modules too? Lowers
  ## the declarations of other modules on the way.
  var n = n
  var nested = 0
  while true:
    case n.kind
    of ParLe:
      if isLiftedClosureTuple(n):
        found = true
        skip n
      elif n.stmtKind in {MacroS, TemplateS}:
        skip n
      elif n.stmtKind in {ProcS, FuncS, MethodS, ConverterS, IteratorS, TypeS} and isGenericDecl(n):
        skip n
      else:
        if n.typeKind in RoutineTypes and (isClosure(n) or itertypeNeedsTuple(n)):
          found = true
        inc n
        inc nested
        continue
    of ParRi:
      inc n
      dec nested
    of Symbol:
      sweepForeignSym c, n.symId, found
      inc n
    of EofToken:
      break
    else:
      inc n
    if nested <= 0: break

proc capturesDirectLocal(n: Cursor): bool =
  ## `n` is a `stmts`: is one of the locals that are its direct sons captured? They
  ## are then in the scope of all of its sons, and it can be hoisted only as a whole.
  var decls = initHashSet[SymId]()
  var it = n
  inc it
  while it.hasMore:
    if it.stmtKind in {VarS, LetS, CursorS, PatternvarS}:
      let s = it.firstSon
      if s.kind == SymbolDef: decls.incl s.symId
    skip it
  result = false
  if decls.len > 0:
    var own = initHashSet[SymId]()
    var m = n
    scanCapture m, 0, true, decls, own, result

proc hoistedName(c: var Context): SymId =
  result = pool.syms.getOrIncl("`modscope." & $c.counter & "." & c.thisModuleSuffix)
  inc c.counter

proc addHoistedProcHead(dest: var TokenBuf; name: SymId; retType: Cursor; info: PackedLineInfo) =
  dest.addSymDef name, info
  dest.addDotToken() # no export marker
  dest.addDotToken() # no pattern
  dest.addDotToken() # no generic params
  dest.copyIntoKind ParamsU, info: discard
  if cursorIsNil(retType):
    dest.addDotToken()
  else:
    dest.addSubtree retType
  dest.copyIntoKind PragmasU, info: discard
  dest.addDotToken() # no effects

proc copyUngloballed(dest, globals: var TokenBuf; n: var Cursor; depth: int) =
  ## Copies module-level code to be the body of a routine. Its globals must not
  ## become statics of that routine: the rest of the module names them. So the
  ## declarations go to `globals` and leave an assignment here.
  if n.kind != ParLe:
    dest.takeToken n
  elif depth == 0 and n.stmtKind in {GvarS, GletS, TvarS, TletS}:
    let info = n.info
    let tag = n
    inc n
    let name = n.symId
    globals.add tag
    globals.takeTree n # name
    globals.takeTree n # export marker
    globals.takeTree n # pragmas
    globals.takeTree n # type
    globals.addDotToken()
    globals.addParRi()
    if n.kind == DotToken:
      inc n
    else:
      dest.copyIntoKind AsgnS, info:
        dest.addSymUse name, info
        dest.takeTree n
    skipParRi n
  else:
    let d = if isRoutineDecl(n): depth + 1 else: depth
    dest.takeToken n
    while n.hasMore:
      copyUngloballed dest, globals, n, d
    dest.takeParRi n

proc hoistToplevel(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## Module-level code has locals too: the ones in a `block`, `for`, `while`, `if`,
  ## `try`, `case` around them. A closure over one needs an environment in a routine
  ##  to live in, and none is around. The statement becomes the body of a routine of
  ## its own, called in its place: from there on it is what the same code in a
  ## routine is, including where the locals die.
  ##
  ##   block:                    proc `modscope.0() =
  ##     var seen = false   ==>    block:
  ##     ...                         ...
  ##                             `modscope.0()
  let info = n.info
  let name = hoistedName(c)
  var globals = createTokenBuf(16)
  globals.addParLe StmtsS, info
  var decl = createTokenBuf(64)
  decl.copyIntoKind ProcS, info:
    addHoistedProcHead decl, name, default(Cursor), info
    decl.copyIntoKind StmtsS, info:
      copyUngloballed decl, globals, n, 0
  var sig = createTokenBuf(16)
  sig.copyIntoKind ProcS, info:
    addHoistedProcHead sig, name, default(Cursor), info
    sig.addDotToken()
  programs.publish name, sig, SemcheckSignatures
  globals.addParRi()
  if globals.len > 2:
    var g = beginRead(globals)
    tr c, dest, g
    endRead(globals)
  var m = beginRead(decl)
  trProc c, dest, m
  endRead(decl)
  dest.copyIntoKind CallS, info:
    dest.addSymUse name, info

proc hoistGlobalInit(c: var Context; dest: var TokenBuf; n: var Cursor) =
  ## `let g = (block: ...)`: the value is hoisted, the global stays.
  ##
  ##   glet g = `modscope.0()   with   proc `modscope.0(): T = result = (block: ...)
  let info = n.info
  let name = hoistedName(c)
  let tag = n
  inc n
  var head = createTokenBuf(16)
  head.add tag
  head.takeTree n # name
  head.takeTree n # export marker
  head.takeTree n # pragmas
  let typ = n
  head.takeTree n # type
  let res = pool.syms.getOrIncl("`modres." & $c.counter)
  inc c.counter
  var decl = createTokenBuf(64)
  decl.copyIntoKind ProcS, info:
    addHoistedProcHead decl, name, typ, info
    decl.copyIntoKind StmtsS, info:
      decl.copyIntoKind ResultS, info:
        decl.addSymDef res, info
        decl.addDotToken()
        decl.addDotToken()
        decl.addSubtree typ
        decl.addDotToken()
      decl.copyIntoKind AsgnS, info:
        decl.addSymUse res, info
        decl.takeTree n
      decl.copyIntoKind RetS, info:
        decl.addSymUse res, info
  skipParRi n
  var sig = createTokenBuf(16)
  sig.copyIntoKind ProcS, info:
    addHoistedProcHead sig, name, typ, info
    sig.addDotToken()
  programs.publish name, sig, SemcheckSignatures
  var m = beginRead(decl)
  trProc c, dest, m
  endRead(decl)
  head.copyIntoKind CallS, info:
    head.addSymUse name, info
  head.addParRi()
  var h = beginRead(head)
  tr c, dest, h
  endRead(head)

proc trToplevel(c: var Context; dest: var TokenBuf; n: var Cursor) =
  if n.kind == ParLe and n.stmtKind == StmtsS:
    if capturesDirectLocal(n):
      hoistToplevel c, dest, n
    else:
      copyInto dest, n:
        while n.hasMore:
          trToplevel c, dest, n
  elif n.kind == ParLe and n.stmtKind in {GvarS, GletS, TvarS, TletS} and capturesToplevelLocal(n):
    hoistGlobalInit c, dest, n
  elif n.kind == ParLe and not isRoutineDecl(n) and n.stmtKind != TypeS and capturesToplevelLocal(n):
    hoistToplevel c, dest, n
  else:
    tr c, dest, n

proc elimLambdas*(pass: var Pass) =
  var n = pass.n  # Extract cursor locally
  var c = Context(counter: 0, typeCache: createTypeCache(), thisModuleSuffix: pass.moduleSuffix)
  c.coroCtx = coro_transform.Context(
    thisModuleSuffix: pass.moduleSuffix,
    typeCache: createTypeCache(),   # placeholder; swapped with c.typeCache per call
    coroTypes: createTokenBuf(10),
    continuationProcImpl: coro_transform.generateContinuationProcImpl(),
    hooks: lambdaHooks()
  )
  c.typeCache.openScope()
  # Before any type is asked for. A module can hold or pass closures with no
  # closure proc of its own, or declare just the type: pass 2 has to run for them
  # as well, or the type and its uses disagree across modules.
  var reachesClosure = false
  sweepClosures c, n, reachesClosure
  if reachesClosure: c.hasClosures = true
  copyInto pass.dest, n:
    while n.hasMore:
      trToplevel c, pass.dest, n
  propagateCapturers c
  c.typeCache.closeScope()

  # second pass: generate environments and rewrite closure types/symbols.
  # Triggered by captures OR any closure-proc declaration / closure-typed nil:
  # pass 1's `trNil` wraps `(nil ClosureProc)` in a `tupconstr`, and `trProc`
  # marks `.closure` procs whose usages need tuple wrappers — both require
  # pass 2 to rewrite the surrounding proctypes/calls so types and values agree.
  if c.localToEnv.len > 0 or c.hasClosures:
    # some closure usage has been found, so we need to generate environments
    c.typeCache.openScope()
    let cap = pass.dest.len
    var oldDest = move pass.dest
    pass.dest = createTokenBuf(cap)
    var n2 = beginRead(oldDest)
    assert n2.stmtKind == StmtsS
    pass.dest.add n2 # stmts opener
    inc n2
    genObjectTypes(c, pass.dest)
    # Walk statements into a side buffer so we can prepend any
    # `.closure` iter coro frame types that `transformClosureIter`
    # accumulates during the walk. The state procs and wrappers
    # reference those types, so they must appear FIRST in the output
    # (alongside the env types).
    var stmtsBuf = createTokenBuf(cap)
    while n2.hasMore:
      tre(c, stmtsBuf, n2)
    # Publish the rewritten iter signatures NOW — `shouldPublish`
    # `start` offsets index into stmtsBuf. Doing this earlier would
    # change `tryLoadSym(iterSym)` mid-pass and confuse the
    # iter-sym-as-value check; deferring until after the walk keeps
    # the pass internally consistent. Order also matters: flush
    # BEFORE concatenating stmtsBuf into pass.dest so the indices
    # stay valid.
    for entry in c.coroCtx.shouldPublish:
      var buf = createTokenBuf(16)
      buf.copyTree stmtsBuf.cursorAt(entry.start)
      endRead(stmtsBuf)
      publishSignature buf, entry.sym, 0
    pass.dest.add c.coroCtx.coroTypes
    pass.dest.add stmtsBuf
    pass.dest.takeParRi n2
    endRead(oldDest)
    c.typeCache.closeScope()

  #echo "PRODUCED ", toString(pass.dest, false)
