# Regression: a top-level `const` whose value is built at run time.
#
# `const Registry = [Bundle(name: "a", sources: @["x"]), ...]` — the `@[...]` is a call,
# so xelim hoists each one into a temp (`x.N`) in the module's init body, and the const's
# `(aconstr ...)` names those temps. `trToplevel` kept the `const` itself at the top level,
# where aowlc turns a non-constant initializer into an assignment in `aowlc_init`: a
# separate function from the init proc the temps live in. gcc then met
# `'X60Qx_1' undeclared (first use in this function)` (the `content` mod).
#
# A const with such a value is now lowered like a global with a call initializer: a bare
# declaration at the top and the assignment inside the init proc, after its temps.
import std/syncio

type
  Bundle = object
    name: string
    sources: seq[string]

const
  Registry = [
    Bundle(name: "a", sources: @["x"]),
    Bundle(name: "b", sources: @["y", "z"])]

proc total(): int =
  var i = 0
  while i < Registry.len:
    result = result + Registry[i].sources.len
    inc i

echo "total=", total()
echo "second=", Registry[1].name, ":", Registry[1].sources[1]
