#!/usr/bin/env bash
# Build aifhexer — the aowl lowering pass, seeded from Araq's nimony/hexer.
#
# aifhexer owns the lowering passes under src/ (the 25 files that inject ARC,
# lift closures, inline iterators, lower exceptions, monomorphise, DCE, and emit
# the .c.aif tree). It reuses nimony's shared compiler library (lib/models/njvl/
# nimony/…) via $NIMONY_SRC until an aowl-owned core exists — the infra is copied
# into .build and our src/ is overlaid on top so intra-tree `../hexer` references
# resolve to our copies consistently.
set -e
NIMONY_SRC="${NIMONY_SRC:-$HOME/nimony/src}"
NIM="${NIM:-$HOME/Nim/bin/nim}"
ROOT="$(cd "$(dirname "$0")" && pwd)"
BUILD="$ROOT/.build"
[ -d "$NIMONY_SRC" ] || { echo "aifhexer: NIMONY_SRC not found: $NIMONY_SRC" >&2; exit 1; }
if [ "$1" = "--fresh" ] || [ ! -d "$BUILD" ]; then
  rm -rf "$BUILD"; cp -r "$NIMONY_SRC" "$BUILD"
fi
cp "$ROOT"/src/*.nim "$BUILD/hexer/"          # overlay OUR lowering passes
[ -f "$ROOT/src/nim.cfg" ] && cp "$ROOT/src/nim.cfg" "$BUILD/hexer/"
mkdir -p "$ROOT/bin"
"$NIM" c -d:release --hints:off --warnings:off -o:"$ROOT/bin/aifhexer" "$BUILD/hexer/hexer.nim"
echo "built $ROOT/bin/aifhexer"
