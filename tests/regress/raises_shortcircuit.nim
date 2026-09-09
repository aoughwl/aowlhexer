# Regression: a `{.raises.}` call on the RIGHT of a short-circuit `or`/`and`.
#
# `eraiser` rewrites such a call into `(expr (stmts (cursor :`canRaise.N …
# (call …)) (if (failed `canRaise.N) …)) `canRaise.N)`. `xelim`'s `or`/`and`
# lowering used to HOIST that `cursor` decl out of the operand, which lost the
# symbol twice over: `typenav` could no longer find it (`[Bug] could not find
# symbol: `canRaise.N`) and `constparams` no longer saw the decl-with-call
# shape it needs to rewrite the call to its error/value tuple.
#
# On the LEFT of the operator the same call always compiled, which is what
# makes this a lowering bug and not a semantic one.
#
# The gate is BEHAVIOURAL, not a byte comparison: nimony's own hexer aborts on
# this input, so there is no reference tree to diff against. `sideEffects`
# counts calls to `mayRaise`, so the printed numbers prove short-circuit
# evaluation survived the lowering — the operand must run exactly when the
# operator says it does, and not once more.
import std/syncio

var sideEffects = 0

proc mayRaise(x: int): bool {.raises.} =
  inc sideEffects
  if x < 0: raise ValueError
  result = x > 0

proc runOr(flag: bool; v: int): int {.raises.} =
  if flag or mayRaise(v): result = 1
  else: result = 2

proc runAnd(flag: bool; v: int): int {.raises.} =
  if flag and mayRaise(v): result = 1
  else: result = 2

proc main() =
  try:
    echo runOr(true, 1), " se=", sideEffects    # `or` short-circuits: rhs skipped
    echo runOr(false, 1), " se=", sideEffects   # `or` evaluates the rhs
    echo runAnd(false, 1), " se=", sideEffects  # `and` short-circuits: rhs skipped
    echo runAnd(true, 0), " se=", sideEffects   # `and` evaluates the rhs
    echo runOr(false, -1)                       # the rhs raises: propagate
  except:
    echo "raised se=", sideEffects

main()
