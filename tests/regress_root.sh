#!/usr/bin/env bash
# tests/regress_root.sh -- regressions built and RUN by the installed aowlmony compiler with the hexer
# under test copied in. regress_stack's backend has no closures, which is what these are about.
#
#   AOWLMONY_ROOT=<root> AOWL_HEXER=<hexer exe> bash tests/regress_root.sh
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="${AOWLMONY_ROOT:?set AOWLMONY_ROOT}"
WORK="$(cygpath -m "$(mktemp -d)")"
cp -r "$SRC/." "$WORK/root"
[ -n "${AOWL_HEXER:-}" ] && cp "$AOWL_HEXER" "$WORK/root/bin/hexer.exe"
export PATH="/c/msys64/ucrt64/bin:$PATH"
pass=0; fail=0
for e in "$HERE"/regress_root/*.expected; do
  name="$(basename "${e%.expected}")"
  (cd "$HERE/regress_root" && "$WORK/root/bin/aowlmony.exe" c --cc:gcc --nimcache:"$WORK/$name" -o:"$WORK/$name.exe" "$name.aowl" >"$WORK/$name.log" 2>&1)
  out="$("$WORK/$name.exe" 2>&1 | tr -d '\r')"
  if [ "$out" = "$(tr -d '\r' < "$e")" ]; then pass=$((pass+1)); else echo "FAIL $name"; tail -3 "$WORK/$name.log"; echo "$out" | tail -3; fail=$((fail+1)); fi
done
rm -rf "$WORK"
echo "regress_root: $pass passed, $fail failed"
[ "$fail" = 0 ]
