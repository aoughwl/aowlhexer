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

## Roadmap

Own it incrementally: rewrite passes onto an aowl-owned core (dropping the
`$NIMONY_SRC` dependency), then retarget the shared infra to the aowl AIF
libraries. Paired with [aiflib](https://github.com/aoughwl/aiflib) (the runtime
ARC injects calls into), this removes the last nimony dependencies from native
codegen.

## License

MIT (the vendored passes are © Andreas Rumpf, MIT, per nimony's license).
