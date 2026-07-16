# aowlhexer

The **aowl lowering pass** — it takes a semantically-checked AIF module
(`.s.aif`, the aowl intermediate format) and lowers it to the C-shaped
`.c.aif` that the native backend ([nifc/aifc](https://github.com/aoughwl/aifc))
prints to C. It is seeded from Andreas Rumpf's `hexer` in
[nimony](https://github.com/nim-lang/nimony) and is being progressively
aowl-owned.

## What it does — the hard part of the compiler

`aowlhexer` is where the genuinely difficult compiler work happens, so that the
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
are what aowlhexer owns and will progressively rewrite. The shared compiler
library (NIF/AIF reader, symbol tables, config, models) is reused from a
`nimony` source checkout via `$NIMONY_SRC` until an aowl-owned core exists — the
build copies it into `.build/` and overlays `src/` on top so intra-tree
`../hexer` references resolve to our copies.

## Build

Needs classic Nim and a nimony source checkout:

```sh
NIMONY_SRC=~/nimony/src ./build.sh          # → bin/aowlhexer
NIMONY_SRC=~/nimony/src ./build.sh --fresh   # re-copy the shared infra first
```

## Use

```sh
bin/aowlhexer c module.s.aif    # lower a semchecked module to .c.aif
bin/aowlhexer d a.aif b.aif …   # dead-code elimination across modules
```

Drop-in for nimony's `hexer`: the [aifmony](https://github.com/aoughwl/aifmony)
driver injects `bin/aowlhexer` in place of `hexer` (via nimony's
`findTool("hexer")` lookup), so a full build reads
`.nim → nifparser → sem → aowlhexer → aowlc → gcc`.

## Verified

Built from Araq's passes, `aowlhexer` produces the same `.c.aif` as nimony's
`hexer`, and in the aifmony pipeline the resulting native binaries return correct
results (`fib(20)=6765`, `ack(3,4)=125`, `fib(25)=75025`). It is the lowering
stage in aifmony's default pipeline today.

## An IR optimizer was prototyped, then removed

An `aifopt` pass (dead-code / dead-var / dead-label elimination, nested-`stmts`
flattening, constant folding, and a move-aware `=destroy` elision) was built to
clean up the slack stock hexer/lengc leaves in the `.c.aif`. **It was removed.**
Measured by disassembly, `gcc -O2` subsumes all of it: dead code goes at any
`-O`, and the move/destroy ARC redundancy goes at `-O2` (gcc inlines the small
in-TU `=destroy`, const-propagates the `nil` from the inlined `=wasMoved`, and
elides the call — 2 redundant `=destroy` calls at `-O0`/`-O1` → 0 at `-O2`).
lengc's own C output carries the identical dead code, so Araq *deliberately*
defers local cleanup to the C optimizer. The pass also stripped the NIF index, so
its output wasn't consumable by the real toolchain. Net-negative on the
`aowlc → gcc` path — gone.

## Roadmap — where a Nim-level optimizer genuinely beats `gcc -O2`

Peephole/DCE/local-ARC is a losing game against gcc. The real frontier is
**high-level, semantic** transformations gcc cannot reconstruct from lowered C,
operating on the *typed* `.s.aif` before lowering — seq/string preallocation
(`result.add` loop → one `newSeq`), bounds/overflow-check elimination via range
invariants, cross-module ARC elision and devirtualization. That belongs in
`aowlsem`, not here. This repo's own path forward is to own the lowering passes
incrementally onto an aowl core (dropping the `$NIMONY_SRC` dependency).

## License

MIT (the vendored passes are © Andreas Rumpf, MIT, per nimony's license).
