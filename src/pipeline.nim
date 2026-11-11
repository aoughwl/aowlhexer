#
#
#           Hexer Compiler
#        (c) Copyright 2024 Andreas Rumpf
#
#    See the file "license.txt", included in this
#    distribution, for details about the copyright.
#

import std / [assertions, tables, hashes, sets, syncio]
include ".." / lib / nifprelude
include ".." / lib / compat2

import ".." / nimony / [nimony_model, programs, decls, typeprops]
import hexer_context, iterinliner, desugar, xelim, duplifier, lifter, destroyer,
  constparams, vtables_backend, eraiser, lambdalifting, cps, passes,
  funcsummary, intramodinliner, arcopt
# `arcopt` runs on the final NIFC (try/finally already lowered to explicit
# control flow). It is the BasicBlock-based pass ported from the battle-tested
# `nim/compiler/optimizer.nim`: a stack of basic blocks each owning a pending
# `=wasMoved` list, cleared on return/break/loop and intersected only at
# exhaustive joins. (The earlier tracker-based `shoggoth/arcopt.nim` unioned
# positions across joins and propagated moved-state into nested branches, which
# let a diverging branch's destroy elide a parent `=wasMoved` → double-free;
# it has been removed in favour of this one.)
when defined(verifyArc):
  import std / syncio
  import ".." / nimony / verify_arc

proc publishHooks*(n: var Cursor) =
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
      n.into:
        while n.hasMore: publishHooks(n)
  of ParRi:
    raiseAssert "BUG: unexpected ParRi in publishHooks"
  else:
    inc n

proc liftClassDestroyers(n: var Cursor; lifter: var LiftingCtx; keep: var seq[TokenBuf]) =
  ## A vtable is written where its class is declared, so that is where its
  ## destructor has to exist. The frontend only forges one for what it sees as not
  ## trivial, and a closure in a field is trivial to it: lowered, the class holds a
  ## reference to an environment. Nothing else is sure to ask for the hook here, as
  ## the code that drops the last reference can be in another module.
  case n.kind
  of ParLe:
    case n.stmtKind
    of TypeS:
      let d = asTypeDecl(n)
      if not d.isGeneric and d.name.kind == SymbolDef and d.body.typeKind == ObjectT and hasRtti(d.name.symId):
        var buf = createTokenBuf(1)
        buf.addSymUse d.name.symId, n.info
        keep.add ensureMove buf
        discard getDestructor(lifter, beginRead(keep[keep.len-1]), n.info)
      skip n
    of TemplateS, MacroS, EmitS:
      skip n
    of ProcS, FuncS, MethodS, ConverterS, IteratorS:
      if asRoutine(n).isGeneric:
        skip n
      else:
        n.into:
          while n.hasMore: liftClassDestroyers(n, lifter, keep)
    else:
      n.into:
        while n.hasMore: liftClassDestroyers(n, lifter, keep)
  of ParRi:
    raiseAssert "BUG: unexpected ParRi in liftClassDestroyers"
  else:
    inc n

proc transform*(c: var EContext; n: Cursor; moduleSuffix: string; bits: int): TokenBuf =
  # Prepare initial buffer from elimForLoops
  var n = n
  var dest = createTokenBuf(300)
  elimForLoops(c, dest, n)
  var initialBuf = move dest

  # Initialize the Pass pipeline
  var pass = initPass(initialBuf, moduleSuffix, "desugar", bits)

  # Pass 1: Desugar
  desugar(pass, c.activeChecks)

  # Pass 3: Lambda Lifting
  pass.prepareForNext("lambdalift")
  elimLambdas(pass)

  # Pass 6: Inject Raising Calls (Exception Handling)
  pass.prepareForNext("eraiser")
  var needsXelimIgnored = false
  injectRaisingCalls(pass, c.bits div 8, needsXelimIgnored)

  # Pass 4: Lower Expressions (first time)
  pass.prepareForNext("xelim1")
  lowerExprs(pass)

  # Pass 5: Inject Duplication Points
  pass.prepareForNext("duplifier")
  injectDups(pass, c.liftingCtx)


  # Pass 7: Lower Expressions (second time, after raises)
  pass.prepareForNext("xelim2")
  lowerExprs(pass)

  # Pass 8: Inject Destructors (RAII/Cleanup)
  pass.prepareForNext("destroyer")
  injectDestructors(pass, c.liftingCtx)

  regenerateStaleHooks c.liftingCtx[], pass.dest
  block:
    var keep: seq[TokenBuf] = @[]
    var scan = beginRead(pass.dest)
    liftClassDestroyers scan, c.liftingCtx[], keep
    endRead(pass.dest)
    genMissingHooks c.liftingCtx[]

  # Special handling: Merge generated hooks
  assert pass.dest[pass.dest.len-1].kind == ParRi
  shrink(pass.dest, pass.dest.len-1)

  if c.liftingCtx[].dest.len > 0:
    var hookReader = beginRead(c.liftingCtx[].dest)
    #echo "HOOKS: ", toString(hookReader)
    publishHooks hookReader
    endRead(c.liftingCtx[].dest)

  pass.dest.add move(c.liftingCtx[].dest)
  pass.dest.addParRi()

  when defined(verifyArc):
    # Verify RC-op consistency on the post-destroyer IR. Gated on
    # `-d:verifyArc`. Currently the verifier runs straight-line analysis
    # only — no CFG/NJVL meet across branches yet — so it false-positives
    # on multi-branch destroyer output. We dump findings to stderr so
    # they can be triaged without failing the build.
    block:
      var arcErrs = analyzeArc(pass.dest, pass.moduleSuffix)
      if arcErrs.len > 0:
        stderr.writeLine "verify_arc diagnostics for ", pass.moduleSuffix, ":"
        stderr.writeLine toString(arcErrs, false)

  pass.prepareForNext("cps")
  transformToCps(pass)

  # Pass 9: Transform VTables (Virtual Table Backend)
  var needsXelimAgain = false
  pass.prepareForNext("vtables")
  transformVTables(pass, needsXelimAgain)

  # Pass 10: Inject Const Param Dereferences
  pass.prepareForNext("constparams")
  injectConstParamDerefs(pass, c.bits div 8, needsXelimAgain)

  # Final pass: Lower expressions and casts.
  # LowerCasts mode also lowers expressions, so this replaces
  # the previously conditional xelim_final pass.
  pass.prepareForNext("xelim_final")
  lowerExprs(pass, LowerCasts)
  pass.finishPass()

  result = ensureMove(pass.dest)

proc optimizeLengOutput*(buf: var TokenBuf; moduleSuffix: string; bits: int) =
  ## Optimizations over the generated Lengc tree. These run after `lengcgen`
  ## has emitted the final Lengc module, so they never see pre-Leng constructs
  ## such as try/finally.
  runArcopt(buf, moduleSuffix, bits)
  annotateFunctionSummaries(buf)
  intraModuleInline(moduleSuffix, buf)
