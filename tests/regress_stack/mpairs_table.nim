# Regression: the front end's output for `mpairs` over a Table left the loop
# variables typed with the iterator's own type parameters (`(mut V.15)`, and
# `k` with no type at all).  Two hexer passes then walked off the end:
#   * iterinliner asserted on a `for` whose iterable is not a call, and
#   * constparams/hsizeof spun forever in getSize/typeSectionMode, because a
#     parameter type that is a Symbol but not a type declaration never moved
#     the alias-chain counter.
# The hexer-side guards are in src/hsizeof.nim (both walks bounded, a symbol that
# is not a type declaration means "unknown size") and src/constparams.nim. This
# program stays RED until the front end substitutes the iterator's type
# parameters for `mpairs`; it is the smallest input that reaches the pair.
import std/tables

var t = initTable[int, int]()
t[1] = 2
for k, v in mpairs(t):
  v = v + k
  echo k, " ", v
