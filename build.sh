#!/usr/bin/env bash
# Build aowlhexer — the aowl lowering pass, seeded from Araq's nimony/hexer.
#
# aowlhexer owns the lowering passes under src/ (the 25 files that inject ARC,
# lift closures, inline iterators, lower exceptions, monomorphise, DCE, and emit
# the .c.aif tree). It reuses nimony's shared compiler library (lib/models/njvl/
# nimony/…) via $NIMONY_SRC until an aowl-owned core exists — the infra is copied
# into .build and our src/ is overlaid on top so intra-tree `../hexer` references
# resolve to our copies consistently.
set -e
NIMONY_SRC="${NIMONY_SRC:-$HOME/nimony/src}"
# A `nim` on PATH is the normal case (choosenim, a distro package); the
# hard-coded checkout is the fallback, not the other way round. With the order
# reversed, `./build.sh` died on any machine that installs Nim the usual way.
NIM="${NIM:-$(command -v nim || echo "$HOME/Nim/bin/nim")}"
ROOT="$(cd "$(dirname "$0")" && pwd)"
BUILD="$ROOT/.build"
[ -d "$NIMONY_SRC" ] || { echo "aowlhexer: NIMONY_SRC not found: $NIMONY_SRC" >&2; exit 1; }
# A nimony lib with the 1_000_000-token debug cap in cursorToPosition builds a
# hexer that dies with an empty `[Assertion Failure]` (inside the mover's
# isLastReadImpl, the first place a position past 1M tokens is computed) on any
# module whose control-flow buffer is that large -- e.g. a big flattened mod.
# The cap is an arbitrary sanity check; refuse to bake it into the binary.
if grep -qE 'assert result < 1_?000_?000$' "$NIMONY_SRC/lib/nifcursors.nim" 2>/dev/null; then
  echo "aowlhexer: $NIMONY_SRC/lib/nifcursors.nim still has the 1_000_000 token cap in cursorToPosition;" >&2
  echo "           raise it to 100_000_000 first, or the built hexer asserts on large modules" >&2
  exit 1
fi
if [ "$1" = "--fresh" ] || [ ! -d "$BUILD" ]; then
  rm -rf "$BUILD"; cp -r "$NIMONY_SRC" "$BUILD"
fi
cp "$ROOT"/src/*.nim "$BUILD/hexer/"          # overlay OUR lowering passes
[ -f "$ROOT/src/nim.cfg" ] && cp "$ROOT/src/nim.cfg" "$BUILD/hexer/"
mkdir -p "$ROOT/bin"
"$NIM" c -d:release --hints:off --warnings:off -o:"$ROOT/bin/aowlhexer" "$BUILD/hexer/hexer.nim"
echo "built $ROOT/bin/aowlhexer"
