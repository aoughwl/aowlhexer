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

Honest scope: for tiny integer programs `gcc -O2` would erase the *runtime*
difference downstream — but the cleanup is backend-independent (it also shrinks
the JS backend's input and the readable C), applies to un-optimized/debug builds,
and is where hexer output quality is genuinely improved rather than deferred to
the C compiler. It runs by default in the [aifmony](https://github.com/aoughwl/aifmony)
pipeline (disable with `AIFMONY_NO_OPT=1`).

## Roadmap

Own it incrementally: rewrite passes onto an aowl-owned core (dropping the
`$NIMONY_SRC` dependency), then retarget the shared infra to the aowl AIF
libraries. Paired with [aiflib](https://github.com/aoughwl/aiflib) (the runtime
ARC injects calls into), this removes the last nimony dependencies from native
codegen. `aifopt` grows toward the wins gcc *cannot* do — eliding redundant ARC
`=copy`/`=destroy` calls, which are opaque function calls to the C compiler.

## License

MIT (the vendored passes are © Andreas Rumpf, MIT, per nimony's license).
