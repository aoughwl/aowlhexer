#!/usr/bin/env bash
# tests/regress_stack.sh -- regressions that are gated by building and RUNNING a
# program with the aowlmony stack and the hexer under test.
#
#   AOWL_TOOLCHAIN=<toolchain root> AOWL_HEXER=<hexer exe> bash tests/regress_stack.sh
#
# Every case gets a time limit: the failure this directory was created for is a
# hexer that never returns, and a gate that can hang is not a gate.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
T="${AOWL_TOOLCHAIN:-$ROOT/..}"
HEXER="${AOWL_HEXER:-$ROOT/bin/aowlhexer.exe}"
WORK="${AOWLHEXER_STACK_WORK:-$ROOT/.stacktest}"
LIMIT="${LIMIT:-300}"
export PATH="/c/msys64/ucrt64/bin:$PATH" AOWL_HEXER="$HEXER"
pass=0; fail=0
for src in "$ROOT"/tests/regress_stack/*.nim; do
  name="$(basename "$src" .nim)"; d="$WORK/$name"; rm -rf "$d"; mkdir -p "$d"
  log="$( cd "$T/aowlmony/tools/driver" && timeout "$LIMIT" node driver.js "$src" \
      --cwd "$T/aowlmony" --lib "$T/aowlmony/rt/lib" --nc "$d/nc" 2>&1 < /dev/null )"
  rc=$?
  exe="$(echo "$log" | grep -a '^built ' | head -1 | sed 's/^built //' | tr -d '\r')"
  if [ "$rc" = 124 ]; then echo "FAIL $name: no result within ${LIMIT}s (hexer hang)"; fail=$((fail+1)); continue; fi
  if [ -z "$exe" ] || [ ! -f "$exe" ]; then echo "FAIL $name: no executable"; echo "$log" | tail -4 | sed 's/^/     | /'; fail=$((fail+1)); continue; fi
  out="$("$exe" 2>&1)"
  if [ "$(echo "$out" | tr -d '\r')" = "$(cat "$src.expected" 2>/dev/null || cat "${src%.nim}.expected")" ]; then pass=$((pass+1)); else echo "FAIL $name: output differs"; fail=$((fail+1)); fi
done
echo "regress_stack: $pass passed, $fail failed"
[ "$fail" = 0 ]
