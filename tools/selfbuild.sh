#!/usr/bin/env bash
# Build aowlhexer with the aowlmony stack ALONE (aowlparser, aowlsem, an existing aowlhexer, aowlc, gcc;
# no `nim`, no reference compiler). Run it twice for a fixed-point check:
#
#   sh tools/selfbuild.sh <outdir>                       stage 1: the installed hexer lowers the new one
#   AOWL_HEXER=<outdir>/hexer.exe sh tools/selfbuild.sh <outdir2>     stage 2: the stage-1 hexer rebuilds itself
#
# Needs the shared compiler library sources (NIMONY_SRC, default $AOWL_TOOLCHAIN/nimony/src; its nifcursors
# must carry the 100_000_000 token cap) and gcc (mingw-w64 ucrt) on PATH.
# Always builds into a FRESH nimcache: a reused one makes the driver skip the build and hand back a stale exe.
set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd -W 2>/dev/null || pwd)"
OUT="${1:?usage: selfbuild.sh <outdir>}"
T="${AOWL_TOOLCHAIN:-$ROOT/..}"
NIMONY_SRC="${NIMONY_SRC:-$T/nimony/src}"
export PATH="/c/msys64/ucrt64/bin:$PATH"
grep -q "100_000_000" "$NIMONY_SRC/lib/nifcursors.nim" || { echo "selfbuild: $NIMONY_SRC/lib/nifcursors.nim still has the 1_000_000 token cap" >&2; exit 1; }
[ -e "$OUT/nc" ] && { echo "selfbuild: $OUT/nc exists; pass a fresh output directory" >&2; exit 1; }
mkdir -p "$OUT/b" "$OUT/doc"
cp -r "$NIMONY_SRC"/. "$OUT/b/"
cp "$ROOT"/src/*.nim "$OUT/b/hexer/"          # overlay OUR lowering passes
[ -f "$ROOT/src/nim.cfg" ] && cp "$ROOT/src/nim.cfg" "$OUT/b/hexer/"
[ -f "$ROOT/doc/version.md" ] && cp "$ROOT/doc/version.md" "$OUT/doc/" || echo "dev" > "$OUT/doc/version.md"
B="$(cd "$OUT/b" && pwd -W 2>/dev/null || pwd)"
OUTW="$(cd "$OUT" && pwd -W 2>/dev/null || pwd)"
D="$T/aowlmony/tools/driver"
(cd "$D" && node driver.js "$B/hexer/hexer.nim" --cwd "$T/aowlmony" --lib "$T/aowlmony/rt/lib" \
    --path "$B/lib,$B/nimony,$B/models,$B/gear2,$B/hexer" --nc "$OUTW/nc" --exe hexer.exe >"$OUTW/build.log" 2>&1) \
  || { echo "selfbuild failed (see $OUT/build.log)"; tail -8 "$OUT/build.log"; exit 2; }
cp "$OUT"/nc/hexer/hexer.exe "$OUT/hexer.exe" 2>/dev/null || cp "$(ls "$OUT"/nc/*/hexer.exe | head -1)" "$OUT/hexer.exe"
echo "built $OUT/hexer.exe"
