## partialhexer.nim — a standalone "partial hexer" driver.
##
##   partialhexer <main-module.s.nif> [outdir]
##
## Runs ONLY the first five hexer passes over a semchecked `.s.nif`:
##
##   1. elimForLoops       (iterator inlining)
##   2. desugar
##   3. elimLambdas        (lambda lifting / closures)
##   4. injectRaisingCalls (exception lowering)
##   5. lowerExprs         (expression lowering, first xelim)
##
## and STOPS before injectDups — so the output carries NO
## `=dup`/`=destroy`/CPS/vtable machinery. Emits `<name>.px.nif`.
##
## Mirrors `hexer/pipeline.nim` proc `transform` lines 48–72.

const FinMarkerBase* = 0x616F_776C_0000_0000'i64
  ## MUST equal the engine's `values.FinMarkerBase`: the tool plants the marker, the interpreter consumes it.

include ".." / lib / nifprelude
include ".." / lib / compat2

import std/[os, syncio, assertions, envvars]
import symparser, langmodes
import nimony_model, programs, typenav, decls
import hexer_context, passes, iterinliner, desugar, lambdalifting,
  eraiser, xelim, lifter, duplifier, destroyer

## `FinMarkerBase` comes from `interp` — ONE definition, because the engine that
## consumes the marker and the driver that plants it must agree, and a constant
## spelled in two files is how two derivations of one question drift apart.
##
## WHY A `discard` OF AN INT LITERAL. It has to survive pass 8 untouched and it
  ## has to be inert if nobody recognises it. `destroyer.tr`'s `case` over
  ## `stmtKind` is exhaustive and its last branch copies the node verbatim,
  ## walking children — `DiscardS` is in that branch — and an int literal has no
  ## destructor, so `injectDestructors` has nothing to attach to it. An engine
  ## that does NOT know the marker simply discards an integer, which is exactly
  ## the behaviour before this change: unrecognised degrades to today.

proc finMarkerIndex(n: Cursor): int =
  ## `k` if `n` is a placeholder `(stmts (discard <FinMarkerBase + k>) …)`,
  ## else -1. Peeks; never advances the caller's cursor.
  result = -1
  if n.kind != ParLe or n.stmtKind != StmtsS: return
  var c = n
  inc c                               # into (stmts …
  if c.kind != ParLe or c.stmtKind != DiscardS: return
  inc c                               # into (discard …
  if c.kind != IntLit: return
  let v = pool.integers[c.intId]
  if v >= FinMarkerBase: result = int(v - FinMarkerBase)

proc stashFinallies(n: var Cursor; dest: var TokenBuf; stash: var seq[TokenBuf]) =
  ## Half one of the DESTROYER FINALLY GUARD; see restoreFinallies for why.
  ## Replaces every `(fin BODY)` with `(fin (stmts (discard MARKER_k)))`, pushing
  ## BODY onto `stash` in tree order. The marker is what tells `restoreFinallies`
  ## WHICH finally each of the destroyer's inlined copies belongs to — an empty
  ## `(stmts)` left the abnormal-exit sites indistinguishable from any other
  ## empty statement list, which is why the ordering defect could not be fixed.
  if n.kind == ParLe and n.substructureKind == FinU:
    let info = n.info
    dest.add n                        # `(fin`
    inc n
    var b = createTokenBuf(30)
    takeTree(b, n)                    # the finally body, out of the tree
    stash.add ensureMove(b)
    let k = stash.len - 1
    copyIntoKind dest, StmtsS, info:  # `(stmts (discard MARKER_k))` in its place
      copyIntoKind dest, DiscardS, info:
        dest.addIntLit(FinMarkerBase + int64(k), info)
    while n.kind != ParRi: stashFinallies(n, dest, stash)
    inc n
    dest.addParRi()
  elif n.kind == ParLe:
    dest.add n
    n.into:
      while n.hasMore: stashFinallies(n, dest, stash)
    dest.addParRi()
  elif n.kind == ParRi:
    raiseAssert "BUG: unexpected ParRi in stashFinallies"
  else:
    dest.add n
    inc n

proc restoreFinallies(n: var Cursor; dest: var TokenBuf; stash: var seq[TokenBuf];
                      idx: var int; inlineFinallies: bool) =
  ## Half two: put each stashed finally body back into the k-th `(fin …)`.
  ##
  ## WHY THE BODY IS HIDDEN FROM THE DESTROYER AT ALL
  ##
  ## `hexer/destroyer.nim` does not leave try/finally alone. `leaveScope`
  ## INLINES a copy of the finally body into every abnormal exit of the guarded
  ## region — the end of each `except` arm, before a propagating `raise`
  ## (`trRaise`), before a `return` (`trReturn`), before a `break` out
  ## (`leaveNamedBlock`/`leaveAnonBlock`) — and leaves the `(fin …)` clause for
  ## the fall-through path only, because its consumer `nifcgen` runs that clause
  ## only when the body completed normally. Both tvm engines instead implement
  ## `(fin …)` as a real finally that runs on every path, so the destroyer's
  ## output ran the finally TWICE on every abnormal exit. That was
  ## `exceptions/tfinally`: raise → except → "A finally" (inlined) → "A finally"
  ## (the clause).
  ##
  ## The first fix tried was to normalise the tree the other way — sink the
  ## finally into the fall-through end of the try body and drop the clause, so
  ## each of the destroyer's inlined copies is the only copy on its path. It
  ## passes tfinally and is WRONG, because the engines do not execute all of
  ## those copies. eraiser lowers a raising call to
  ## `let e = f(); if failed(e): <inlined finally>; raise e`, and the engines do
  ## not run that `failed` branch at all: a raising call sets `ip.raised` and
  ## unwinds through the engines' own channel, so the copy the destroyer put
  ## before the `raise` is dead code. A `try`/`finally` whose body raises
  ## through a call then printed nothing (probe: tests/semantics/
  ## finally_raise_through_call.nim, finally_nested_raise.nim).
  ##
  ## So neither shape of the destroyer's output matches what the engines
  ## execute. Rather than teach two engines a second, mode-dependent meaning for
  ## one tag, the destroyer is simply never shown the finally body: passes 6 and
  ## 7 still see it (=dup insertion and expression lowering), pass 8 sees
  ## `(fin (stmts))`, inlines that empty body harmlessly onto every abnormal
  ## exit, and the real body is put back afterwards. The engines then apply
  ## their own finally semantics to the one and only copy, exactly as they
  ## already do in the default (non-`--fin`) mode, which reproduces native on
  ## every control-flow probe.
  ##
  ## KNOWN GAP, deliberately taken: a local DECLARED INSIDE a finally body gets
  ## no scope-exit `=destroy`, because pass 8 never walks that body. Nothing
  ## else about the body is affected — passes 1–7 all ran on it — and the
  ## alternative is a destroyer that duplicates control flow the engines then
  ## re-run.
  ##
  ## The pairing is positional: `injectDestructors` copies `try`/`fin` nodes in
  ## order and never invents or drops one (an inlined finally is emitted as a
  ## bare `(stmts …)`, never wrapped in `fin`), so the k-th `(fin …)` out is the
  ## k-th `(fin …)` in.
  if n.kind == ParLe and n.substructureKind == FinU:
    dest.add n                        # `(fin`
    inc n
    let k = finMarkerIndex(n)         # the placeholder `(stmts (discard MARK))`
    skip n
    if k >= 0 and k < stash.len:
      dest.add stash[k]               # the clause: body ONLY, marker dropped —
      inc idx                         # running the clause must not discharge it
    else:
      raiseAssert "BUG: finally stash exhausted in restoreFinallies"
    while n.kind != ParRi: restoreFinallies(n, dest, stash, idx, inlineFinallies)
    inc n
    dest.addParRi()
  elif n.kind == ParLe and finMarkerIndex(n) >= 0 and not inlineFinallies:
    # ⚠️ NO LONGER REACHED FROM EITHER ENGINE — both `lowerPartial` (tree-walker)
    # and `compilePartial` (VM) now pass `inlineFinallies = true`. Kept because it
    # is the only description of the tree the VM consumed before the runtime
    # discharge existed, and because `TVM_FIN=2`/the standalone driver still
    # default to it.
    # THE VM DOES NOT WANT THE INLINED COPY. It implements `fin` with a real
    # handler stack (`opSetupTry`/`opPopTry`/`opEndFinally` plus
    # `emitPendingFinallys` for break/continue), so it already runs the clause on
    # every abnormal exit; handing it the destroyer's copy as well makes the
    # finally run TWICE (measured: `ret fin` and `raise fin` both doubled on
    # tests/probes/tfin_destructor_order.nim). Restore the empty placeholder —
    # byte-for-byte the tree the VM lowered before markers existed.
    #
    # ⚠️ SO THE VM STILL HAS THE ORDERING DEFECT, and the two engines now lower
    # `--fin` differently. That is recorded rather than hidden: closing it for the
    # VM means a runtime discharge over statically-emitted bytecode (a new opcode),
    # which is its own change. See OPEN.md #2.
    let info = n.info
    inc n
    skip n                            # drop `(discard MARKER_k)`
    while n.kind != ParRi: skip n
    inc n
    copyIntoKind dest, StmtsS, info:
      discard
  elif n.kind == ParLe and finMarkerIndex(n) >= 0:
    # A BARE placeholder: one of the destroyer's INLINED copies, sitting at an
    # abnormal exit (before a `return`, a `break`, a propagating `raise`, or at
    # the end of an `except` arm) — `leaveScope` emits it and then the scope's
    # destroys, which is precisely native's order and precisely the order the
    # engines could not reproduce. Keep the marker (the engine discharges the
    # try's clause on it) and put the real body after it, so the finally runs
    # HERE, before the destroys, instead of after the body via the clause.
    let k = finMarkerIndex(n)
    dest.add n                        # `(stmts`
    inc n
    takeTree dest, n                  # `(discard MARKER_k)` — the discharge
    if k < stash.len: dest.add stash[k]
    while n.kind != ParRi: restoreFinallies(n, dest, stash, idx, inlineFinallies)
    inc n
    dest.addParRi()
  elif n.kind == ParLe:
    dest.add n
    n.into:
      while n.hasMore: restoreFinallies(n, dest, stash, idx, inlineFinallies)
    dest.addParRi()
  elif n.kind == ParRi:
    raiseAssert "BUG: unexpected ParRi in restoreFinallies"
  else:
    dest.add n
    inc n

proc publishHooksLocal(n: var Cursor) =
  ## Local copy of hexer/pipeline.publishHooks (not exported by that module):
  ## walk the merged hook buffer and `publish` each synthesized routine so its
  ## symbol resolves like any other declared proc (fix #4 finalization).
  ##
  ## ⚠️ NOT a verbatim copy any more, and deliberately. The upstream version walks
  ## a non-routine node with `n.into: while n.hasMore: publishHooks(n)`, whose
  ## epilogue `assert n.kind == ParRi, "into: body must consume all children"` is
  ## the ONLY thing a caller ever sees when it trips: aowlmony's assert handler
  ## prints that sentence to STDOUT and quits 1 — no module name, no tag, no hint
  ## that `--fin` lowering is what died, and the sentence lands in the very stream
  ## a differential gate compares. Measured 2026-08-04 on a `{.raises: Exception.}`
  ## probe: `tvm-interp --fin` produced exactly `[Assertion Failure] into: body
  ## must consume all children` on stdout and nothing on stderr.
  ##
  ## So the descent is spelled out instead of delegated to `into`. It cannot
  ## over-run (the loop terminates on ParRi or EOF), and if the walk does end up
  ## somewhere structurally impossible it SAYS SO on stderr, naming the tag, and
  ## keeps the buffer walkable rather than aborting the process.
  case n.kind
  of ParLe:
    case n.stmtKind
    of ProcS, FuncS, MacroS, MethodS, ConverterS:
      let decl = asRoutine(n)
      var dest = createTokenBuf()
      takeTree(dest, n)
      let sym = decl.name.symId
      publish sym, dest
    else:
      inc n                                   # into the node
      while n.kind != ParRi and n.kind != EofToken:
        publishHooksLocal(n)
      if n.kind == ParRi: inc n               # past the closing paren
  of ParRi:
    # Upstream `raiseAssert`s here. A stray ParRi means the walk is one level out
    # of step; report it and step over rather than killing the run with a sentence
    # that names neither the mode nor the module.
    write stderr, "tvm --fin: partial hexer hook walk hit a stray ')' " &
                  "while publishing synthesized ARC hooks — continuing\n"
    inc n
  else:
    inc n

proc transformPartial*(c: var EContext; n: Cursor; moduleSuffix: string;
                      bits: int; throughDestroyer = false;
                      inlineFinallies = false): TokenBuf =
  ## Replicates pipeline.transform's 1–5 prefix. With `throughDestroyer = false`
  ## (default) it stops before injectDups — the pre-existing `--px` behaviour
  ## (closures / iterators / exceptions, NO `=dup`/`=destroy`). With
  ## `throughDestroyer = true` it continues through injectDups + xelim2 +
  ## injectDestructors and merges the synthesized/published hooks — mirroring
  ## pipeline.transform lines 74–98 — STOPPING before `prepareForNext("cps")`.
  ## This is the pre-cps cut consumed by the fix#4 finalization path.
  ## `TVM_FIN_STAGE=1` narrates the pass sequence on stderr. It exists because
  ## the ONLY failure mode this pipeline has is a hard abort from inside a aowlmony
  ## hexer pass (`assert`/`raiseAssert` -> one sentence on stdout, exit 1), which
  ## names neither the pass nor the module — and the driver has not written a byte
  ## of program output yet, so the caller sees an empty run. With the stage trace
  ## on, the LAST line printed is the pass that died.
  let stageTrace = getEnv("TVM_FIN_STAGE") == "1"
  template stage(name: string) =
    if stageTrace: write stderr, "tvm --fin: " & moduleSuffix & ": " & name & "\n"
  var n = n
  var dest = createTokenBuf(300)
  stage "elimForLoops"
  elimForLoops(c, dest, n)                       # pass 1
  var initialBuf = ensureMove(dest)

  var pass = initPass(initialBuf, moduleSuffix, "desugar", bits)

  stage "desugar"
  desugar(pass, c.activeChecks)                  # pass 2

  pass.prepareForNext("lambdalift")
  stage "elimLambdas"
  elimLambdas(pass)                              # pass 3

  pass.prepareForNext("eraiser")
  var needsXelimIgnored = false
  stage "injectRaisingCalls"
  injectRaisingCalls(pass, c.bits div 8, needsXelimIgnored)  # pass 4

  pass.prepareForNext("xelim1")
  stage "lowerExprs(xelim1)"
  lowerExprs(pass)                               # pass 5

  if not throughDestroyer:
    # Do NOT prepareForNext after the last pass (it would clear dest).
    pass.finishPass()
    return ensureMove(pass.dest)

  # --- fix #4: continue through the destroyer (pre-cps cut) ---------------
  pass.prepareForNext("duplifier")
  stage "injectDups"
  injectDups(pass, c.liftingCtx)                 # pass 6 (=dup insertion)

  pass.prepareForNext("xelim2")
  stage "lowerExprs(xelim2)"
  lowerExprs(pass)                               # pass 7

  # pass 7b: take every finally BODY out of the tree before the destroyer sees
  # it, and put it back in pass 8b. The destroyer inlines a copy of that body
  # onto every abnormal exit of the guarded region, which the engines — whose
  # `(fin …)` is a real finally — then run a second time. See restoreFinallies
  # for the full reasoning and for the one gap this leaves.
  var finStash: seq[TokenBuf] = @[]
  block:
    var fixed = createTokenBuf(pass.dest.len)
    var rd = beginRead(pass.dest)
    stage "stashFinallies"
    stashFinallies(rd, fixed, finStash)
    endRead(pass.dest)
    pass.dest = ensureMove(fixed)

  pass.prepareForNext("destroyer")
  stage "injectDestructors"
  injectDestructors(pass, c.liftingCtx)          # pass 8 (=destroy scope-exit)

  # pass 8b: the finally bodies go back where they came from.
  block:
    var fixed = createTokenBuf(pass.dest.len)
    var rd = beginRead(pass.dest)
    var idx = 0
    stage "restoreFinallies"
    restoreFinallies(rd, fixed, finStash, idx, inlineFinallies)
    endRead(pass.dest)
    pass.dest = ensureMove(fixed)

  # Merge generated hooks (pipeline.transform lines 88–98). Drop the closing
  # `stmts` ParRi, splice in the synthesized-hook buffer (publishing each hook),
  # then re-close. This is done BEFORE the cps/vtable/constparam passes we skip.
  assert pass.dest[pass.dest.len-1].kind == ParRi
  shrink(pass.dest, pass.dest.len-1)

  if c.liftingCtx[].dest.len > 0:
    var hookReader = beginRead(c.liftingCtx[].dest)
    stage "publishHooks"
    publishHooksLocal hookReader
    endRead(c.liftingCtx[].dest)

  pass.dest.add move(c.liftingCtx[].dest)
  pass.dest.addParRi()

  pass.finishPass()
  result = ensureMove(pass.dest)

proc newPartialContext(dir, ext, main: string; bits: int): EContext =
  ## Shared EContext factory for both the standalone driver and the in-process
  ## tvm-vm pipeline (compilePartial).
  result = EContext(dir: dir, ext: ext, main: main,
    nestedIn: @[(StmtsS, SymId(0))],
    typeCache: createTypeCache(),
    pending: createTokenBuf(),
    strLitBuf: createTokenBuf(),
    bits: bits,
    bigEndian: false,
    localDeclCounters: 1000,
    activeChecks: DefaultSettings,
    liftingCtx: createLiftingCtx(main, bits)
  )
  result.typeCache.openScope()

proc hasFlag(f: string): bool =
  result = false
  let ps = commandLineParams()
  for i in 0 ..< ps.len:
    if ps[i] == f: return true

proc runPartialHexer(infile: string; outdir: string) =
  let mp = splitModulePath(infile)
  let dir =
    if outdir.len > 0: outdir
    elif mp.dir.len == 0:
      try: getCurrentDir()
      except: quit "cannot get current working directory"
    else: mp.dir

  let bits = sizeof(int) * 8
  var c = newPartialContext(dir, mp.ext, mp.name, bits)

  # `owningBuf` MUST outlive the run: `root` points into it.
  var owningBuf = createTokenBuf(300)
  var root = setupProgram(infile, infile.changeModuleExt ".x.nif", owningBuf, true)

  let throughDestroyer = getEnv("TVM_FIN") == "1" or hasFlag("--through-destroyer")
  var outBuf = transformPartial(c, root, mp.name, bits, throughDestroyer,
                                inlineFinallies = hasFlag("--inline-finallies"))

  let destName = dir / (mp.name & ".px.nif")
  try:
    writeFile outBuf, destName
  except:
    quit "could not write file: " & destName
  stdout.writeLine "wrote " & destName

proc main() =
  let params = commandLineParams()
  var infile = ""
  var outdir = ""
  for p in params:
    if p.len > 0 and p[0] == '-': continue
    if infile.len == 0: infile = p
    else: outdir = p
  if infile.len == 0:
    quit "usage: partialhexer <main-module.s.nif> [outdir]\n" &
         "  (the outdir is NOT created for you — mkdir -p it first)\n" &
         "  TVM_FIN=1        also run passes 6-8 (=dup / xelim2 / destroyer)\n" &
         "  TVM_FIN_STAGE=1  narrate the pass sequence on stderr. Use this when\n" &
         "                     --fin dies with a bare '[Assertion Failure] …' and\n" &
         "                     exit 1: the LAST stage line names the pass that\n" &
         "                     aborted, which is the whole diagnosis."
  runPartialHexer(infile, outdir)

when isMainModule:
  main()
