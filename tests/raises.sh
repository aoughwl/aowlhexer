#!/usr/bin/env bash
# tests/raises.sh — the `{.raises.}` lowering regressions, gated by RUNNING the
# produced binary.
#
# The other gates here are byte comparisons against nimony's hexer. That works
# only where the reference lowers the input at all. These cases are exactly the
# ones where it does not: nimony's hexer aborts on them, so there is no tree to
# diff and "aowlhexer lowered it" is a claim nothing checks. Compiling the case
# and comparing the program's OUTPUT is the only gate that constrains it — and
# it is the first gate in this repo that runs a produced binary at all, which
# tests/claims.sh has been red about.
#
# HOW THE HEXER IS SUBSTITUTED
#   nimony resolves its tools with `findTool` (nimony/src/lib/tooldirs.nim),
#   which checks `<name>.exe` in the CURRENT DIRECTORY before nimony's own bin/.
#   So a copy of aowlhexer named `hexer.exe` in the work dir — with that dir on
#   PATH, since nifmake execs the bare name it was handed — is the whole trick.
#   Nothing is written into the nimony checkout.
#
#   HEXER=... to gate a different binary (e.g. to prove a case is red before a
#   fix); REF=1 to run the reference hexer instead, which should FAIL.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NIMONY_BIN="${NIMONY_BIN:-$HOME/nimony/bin}"
NIMONY="${NIMONY:-$NIMONY_BIN/nimony}"
HEXER="${HEXER:-$ROOT/bin/aowlhexer}"
[ "${REF:-0}" = 1 ] && HEXER="$NIMONY_BIN/hexer"
WORK="${AOWLHEXER_RAISES_WORK:-$ROOT/.raisestest}"
CASES="$ROOT/tests/regress"

for c in "$HEXER" "$NIMONY"; do
  [ -x "$c" ] || [ -x "$c.exe" ] || { echo "raises: no binary at $c" >&2; exit 2; }
done
[ -x "$HEXER" ] || HEXER="$HEXER.exe"
[ -x "$NIMONY" ] || NIMONY="$NIMONY.exe"

# Each case is a .nim next to its .expected stdout.
pass=0; fail=0
for src in "$CASES"/*.nim; do
  name="$(basename "$src" .nim)"
  exp="$CASES/$name.expected"
  [ -f "$exp" ] || { echo "raises: $name has no .expected"; fail=$((fail+1)); continue; }
  d="$WORK/$name"
  rm -rf "$d"; mkdir -p "$d"
  cp "$src" "$d/$name.nim"
  cp "$HEXER" "$d/hexer.exe"
  log="$( cd "$d" && PATH="$PWD:$PATH" "$NIMONY" c "$name.nim" 2>&1 )"
  bin="$(find "$d/nimcache" -name "$name.exe" -o -name "$name" -type f 2>/dev/null | head -1)"
  if [ -z "$bin" ]; then
    echo "FAIL $name: no binary produced"
    echo "$log" | tail -5 | sed 's/^/     | /'
    fail=$((fail+1)); continue
  fi
  # CRLF: the produced binary is a Windows console app, the .expected file is
  # LF in git. Compare the text, not the line terminator.
  "$bin" > "$d/$name.out" 2>&1
  if diff -q --strip-trailing-cr "$exp" "$d/$name.out" >/dev/null; then
    pass=$((pass+1))
  else
    echo "FAIL $name: output differs"
    diff --strip-trailing-cr "$exp" "$d/$name.out" | sed 's/^/     | /'
    fail=$((fail+1))
  fi
done

echo ""
echo "$pass/$((pass+fail)) raises cases build and print what they should"
[ "$fail" = 0 ]
