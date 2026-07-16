# aifhexer

The **aowl lowering pass** — it takes a semantically-checked AIF module
(`.s.aif`, the aowl intermediate format) and lowers it to the C-shaped
`.c.aif` that the native backend ([nifc/aifc](https://github.com/aoughwl/aifc))
prints to C. It is seeded from Andreas Rumpf's `hexer` in
[nimony](https://github.com/nim-lang/nimony) and is being progressively
aowl-owned.

## What it does — the hard part of the compiler

`aifhexer` is where the genuinely difficult compiler work happens, so that the
backends downstream can be mere printers:

| pass | effect |
|---|---|
| `destroyer` + `duplifier` + `mover` | **ARC** — destructor calls, `=copy`/`=destroy` hooks, ref-count ops injected |
| `lambdalifting` | closures → plain functions + env structs |
| `iterinliner` | iterators inlined |
| `eraiser` | exceptions → error-code plumbing |
| `inliner` / `dce2` / `constparams` | inlining, dead-code elimination, const-param specialisation |
| `lengcgen` | emit the sized, ARC'd, monomorphised `.c.aif` tree |

Because ARC is injected here, every backend that consumes `.c.aif` gets
**deterministic memory management for free** — this is exactly why
[aifc](https://github.com/aoughwl/aifc) can be a printer.

## Ours vs reused

The 25 lowering passes under `src/` are vendored from Araq's `nimony/hexer` and
are what aifhexer owns and will progressively rewrite. The shared compiler
library (NIF/AIF reader, symbol tables, config, models) is reused from a
`nimony` source checkout via `$NIMONY_SRC` until an aowl-owned core exists — the
build copies it into `.build/` and overlays `src/` on top so intra-tree
`../hexer` references resolve to our copies.

## Build

Needs classic Nim and a nimony source checkout:

```sh
NIMONY_SRC=~/nimony/src ./build.sh          # → bin/aifhexer
NIMONY_SRC=~/nimony/src ./build.sh --fresh   # re-copy the shared infra first
```

## Use

```sh
bin/aifhexer c module.s.aif    # lower a semchecked module to .c.aif
bin/aifhexer d a.aif b.aif …   # dead-code elimination across modules
```

Drop-in for nimony's `hexer`: the [aifmony](https://github.com/aoughwl/aifmony)
driver injects `bin/aifhexer` in place of `hexer` (via nimony's
`findTool("hexer")` lookup), so a full build reads
`.nim → nifparser → sem → aifhexer → aifc → gcc`.

## Verified

Built from Araq's passes, `aifhexer` produces the same `.c.aif` as nimony's
`hexer`, and in the aifmony pipeline the resulting native binaries return correct
results (`fib(20)=6765`, `ack(3,4)=125`, `fib(25)=75025`). It is the lowering
stage in aifmony's default pipeline today.

## Better than stock hexer — the optimization layer (`opt/aifopt.js`)

Stock hexer/lengc lowers *correctly* but leaves measurable slack in the `.c.aif`:
**every** proc it emits carries an unreachable trailing `return result`, the dead
`result` variable behind it, and a dead loop label — plus deeply nested
single-child `(stmts (stmts …))` blocks and un-folded constant arithmetic.
`aifopt` is the fixpoint simplifier a stock pipeline omits. It removes all of it
and re-emits a valid `.c.aif`.

Concretely, the `gcd` proc — **before** (stock hexer → C) and **after** (+aifopt):

```c
NI64 gcd(NI64 a, NI64 b) {          NI64 gcd(NI64 a, NI64 b) {
  NI64 result_0;         // dead      NI64 x = a;
  NI64 x = a;                         NI64 y = b;
  NI64 y = b;                         { while (!(y == 0)) {
  { while (!(y == 0)) {                   NI64 t = y; y = x % y; x = t;
      NI64 t = y; y = x % y; x = t;   } }
  } }                                 return x;
  whileStmtLabel_0: ;    // dead    }
  return x;
  return result_0;       // unreachable
}
```

Measured on real hexer output (`node opt/demo.js`):

| file | IR nodes | dead rets | dead vars | dead labels |
|---|---|---|---|---|
| compute | 486 → 444 (−8.6%) | 12 → 8 | 12 → 8 | 4 → 0 |
| fib | 254 → 241 (−5.1%) | 7 → 5 | 6 → 5 | 1 → 0 |
| mathf | 330 → 317 (−3.9%) | 12 → 10 | 5 → 4 | 1 → 0 |
| **total** | **1070 → 1002 (−6.4%)** | **31 → 23** | **23 → 17** | **6 → 0** |

**8/8** optimized programs return identical results — the cleanup is behaviour-
preserving. Passes: unreachable-code elimination, dead-variable elimination,
dead-label elimination, `(stmts (stmts …))` flattening, integer constant folding,
and algebraic identities (`x+0`, `x*1`, `x*0`, …), run to a fixpoint.

There is also an **ARC pass**, `moveDestroyElim`: hexer's mover emits
`=wasMoved(v)` when a value moves out of `v`, but the destroyer independently
emits `=destroy(v)` at scope exit. Since `=wasMoved` sets `v.data := nil` and
`=destroy` is `if v.data != nil: dealloc`, an `=destroy(v)` that a `=wasMoved(v)`
unconditionally dominates is a provable no-op. aifopt removes it — soundly (an
emptied owner has nothing to free). On a seq round-trip it cuts `=destroy` call
sites 7 → 1.

### Does this actually beat the stock pipeline? (measured — mostly no)

We tested honestly, by disassembly. **`gcc -O2` subsumes all of the above.** Dead
code goes at any `-O`; the move/destroy ARC redundancy goes at `-O2`, because gcc
inlines the small in-TU `=destroy`, const-propagates the `nil` from the inlined
`=wasMoved`, and elides the call:

| opt level | `=destroy` calls left in the round-trip proc |
|---|---|
| `-O0` / `-O1` | **2** (gcc keeps the redundant one) |
| `-O2` / `-O3` | **0** (gcc does the elision itself) |

This is almost certainly **why Araq leaves it**: hexer/lengc emit canonical,
simple C and defer local cleanup to a world-class C optimizer — and lengc's own
output carries the identical dead code. So aifopt's honest value is narrower than
"beats hexer":

- **`-O0`/`-O1` debug builds** — real: fewer instructions, faster debug builds.
- **cross-TU ARC** — when a type's `=destroy` is *not* inlined (large body or a
  different module without LTO), gcc keeps the redundant call and aifopt removes it.
- **backend-independent** — it shrinks the JS backend's input and the readable C.

It runs by default in [aifmony](https://github.com/aoughwl/aifmony)
(`AIFMONY_NO_OPT=1` disables).

## Roadmap — where a Nim-level optimizer genuinely beats `gcc -O2`

Peephole/DCE/local-ARC is a losing game against gcc. The real frontier is
**high-level, semantic** transformations gcc cannot reconstruct from the lowered
C, operating on the *typed* `.s.aif` before lowering:

- **seq/string preallocation & builder fusion** — turn a `result.add(x)` loop
  (which reallocs `O(log n)` times) into one `newSeq(n)`. gcc can't hoist or size
  the alloc; this survives `-O2`.
- **bounds/overflow-check elimination** via range invariants (`for i in 0 ..< s.len: s[i]`).
- **cross-module ARC elision** and devirtualization with whole-program info.

Own the passes incrementally onto an aowl core (dropping `$NIMONY_SRC`), paired
with [aiflib](https://github.com/aoughwl/aiflib). That — not local peephole — is
how "better than hexer" becomes true at `-O2`.

## License

MIT (the vendored passes are © Andreas Rumpf, MIT, per nimony's license).
