#!/usr/bin/env bash
# The lowering differential, run over a REAL program instead of a corpus of
# small cases: the Nimony mods of infiniteless-next.
#
# Corpus cases are short and shallow; the mods are the closest thing this
# toolchain has to production code, and they are the thing that must not
# regress. This seeds from the game's sources (read-only -- nothing is written
# back into that repo) and then runs the same byte-for-byte `.x.nif` comparison
# as tests/differential.sh.
#
# The `-p:` search paths mirror `tools/build_mod.py`'s: nimony's own lib, the
# mod folder, and the ModSdk.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GAME="${INFINITELESS:-$HOME/Documents/infiniteless-next}"
NIMONY_SRC_DIR="${NIMONY_SRC_DIR:-$HOME/nimony/src}"
SDK="$GAME/Packages/com.infiniteless.runtime/ModSdk"
MODS="$GAME/Assets/StreamingAssets/Mods"

[ -d "$MODS" ] || { echo "game: no mods at $MODS (set INFINITELESS)" >&2; exit 2; }
[ -d "$SDK" ]  || { echo "game: no ModSdk at $SDK" >&2; exit 2; }

fail=0
for mod in "$MODS"/*/; do
  [ -f "$mod/mod.json" ] || continue
  id="$(basename "$mod")"
  entry="$mod/$(grep -o '"entry"[^,}]*' "$mod/mod.json" | sed 's/.*"\([^"]*\)"$/\1/')"
  [ -f "$entry" ] || entry="$mod/main.nim"
  [ -f "$entry" ] || { echo "skip $id (no entry)"; continue; }

  # A per-mod work dir: the `-p:` set differs per mod, so the seeds cannot share
  # one nimcache without the search path of whichever mod ran first winning.
  work="$ROOT/.difftest-game/$id"
  echo "=== $id"
  AOWLHEXER_CORPUS="$mod" \
  AOWLHEXER_WORK="$work" \
  AOWLHEXER_NIMFLAGS="-p:$NIMONY_SRC_DIR/lib -p:$mod -p:$SDK" \
    "$ROOT/tests/differential.sh" --jobs 4 || fail=$((fail+1))
done

echo ""
[ "$fail" = 0 ] && echo "every mod lowers identically" || echo "$fail mod(s) FAILED"
[ "$fail" = 0 ]
