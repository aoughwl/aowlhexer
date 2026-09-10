# Regression: `x = f(x)` after anything else has copied `x`.
#
# `mover.singlePath` decides whether an earlier read of a location is its LAST
# read, which lets the duplifier turn that read into a move (`=wasMoved` on the
# source) instead of a copy (`=dup`). Walking forward it used to treat ANY
# assignment whose left-hand side is the location as "the value is dead from
# here on" and stop the walk — looking only at the left-hand side and never at
# the right.
#
# But the right-hand side is evaluated BEFORE the store. In
#
#     let keep = a
#     a = pick(a)
#
# the `a` inside `pick(a)` is a later read, so `let keep = a` is not the last
# one. Stopping at the left-hand side made it look like one, so the lowering
# came out as
#
#     var keep = a            # bit copy, no =dup
#     =wasMoved(addr a)       # <-- BEFORE the call
#     var `lhs = pick(a)      # pick() sees a zeroed `a`
#
# and `pick` took its empty-string branch on a non-empty argument. Silently:
# no error, no crash, just the wrong branch. `let next = f(x); x = next` was
# unaffected, which is what made it look like a language rule rather than a bug.
#
# The gate is BEHAVIOURAL: this is a wrong-answer bug, and the reference hexer
# lowers the input happily — it just lowers it wrong — so only running the
# binary catches it. Under `REF=1` this case must FAIL.
import std/syncio

type Box = object
  item: string

proc pick(b: Box): Box =
  if b.item.len == 0: return Box(item: "EMPTY")
  b

proc twice(s: string): string =
  if s.len == 0: return "EMPTY"
  s & s

proc main() =
  # object with a string field, copied by `let`
  var a = Box(item: "stone")
  let keep = a
  a = pick(a)
  echo "obj let  keep=", keep.item, " a=", a.item

  # the same with `var`
  var b = Box(item: "wood")
  var kept = b
  b = pick(b)
  echo "obj var  kept=", kept.item, " b=", b.item

  # a bare string, no object involved
  var s = "ore"
  let ks = s
  s = twice(s)
  echo "string   ks=", ks, " s=", s

  # the copy is still a copy afterwards: mutating `a` must not touch `keep`
  a = Box(item: "iron")
  echo "after    keep=", keep.item, " a=", a.item

  # no prior copy: this path was always correct and must stay correct
  var c = Box(item: "clay")
  c = pick(c)
  echo "nocopy   c=", c.item

main()
