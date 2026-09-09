#!/usr/bin/env bash
# The lowering differential: nimony's `hexer` is the reference implementation
# and aowlhexer must lower the same typed input to the same tree.
#
# aowlhexer's src/ is a fork of Araq's nimony/src/hexer, so "does it still agree
# with the thing it was forked from" is the one gate that actually constrains a
# lowering pass. Reading the passes does not: they are 500KB of ARC injection,
# closure lifting and monomorphisation whose output is only meaningful against
# a reference.
#
# HOW IT WORKS
#   phase 1 (seed)    run `nimony check` over a corpus of .nim sources into ONE
#                     shared nimcache. That leaves a typed `.s.nif` per module —
#                     corpus modules AND every stdlib module they pull in, each
#                     appearing exactly once because the cache is content-keyed.
#   phase 2 (compare) run BOTH hexers over every `.s.nif` with the flags the
#                     real driver uses (see the `(cmd :hexer ...)` line in any
#                     nimcache `.final.build.nif`) and require the lowered
#                     `.x.nif` and the `.dce.nif` analysis to be byte-identical.
#
# Phase 1 is the slow half and is cached: re-running only re-seeds what is
# missing. Phase 2 is seconds.
#
# Usage:
#   tests/differential.sh                 # seed (if needed) + compare
#   tests/differential.sh --compare-only  # skip seeding, use the existing cache
#   tests/differential.sh --corpus DIR    # a different corpus of .nim sources
#   tests/differential.sh --jobs N        # seeding parallelism (default 8)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
NIMONY_BIN="${NIMONY_BIN:-$HOME/nimony/bin}"
REF="${REF_HEXER:-$NIMONY_BIN/hexer}"
OURS="${OURS_HEXER:-$ROOT/bin/aowlhexer}"
CORPUS="${AOWLHEXER_CORPUS:-$HOME/aowlsem.ghfresh/tests/corpus}"
WORK="${AOWLHEXER_WORK:-$ROOT/.difftest}"
JOBS=8
COMPARE_ONLY=0
NIMFLAGS="${AOWLHEXER_NIMFLAGS:-}"

while [ $# -gt 0 ]; do
  case "$1" in
    --compare-only) COMPARE_ONLY=1; shift;;
    --corpus) CORPUS="$2"; shift 2;;
    --jobs) JOBS="$2"; shift 2;;
    --work) WORK="$2"; shift 2;;
    *) echo "unknown argument: $1" >&2; exit 2;;
  esac
done

command -v "$REF" >/dev/null 2>&1 || [ -x "$REF" ] || [ -x "$REF.exe" ] || {
  echo "differential: no reference hexer at $REF (set REF_HEXER)" >&2; exit 2; }
[ -x "$OURS" ] || [ -x "$OURS.exe" ] || {
  echo "differential: no aowlhexer at $OURS — run ./build.sh" >&2; exit 2; }
[ -d "$CORPUS" ] || { echo "differential: no corpus at $CORPUS" >&2; exit 2; }

NIMONY="${NIMONY:-$NIMONY_BIN/nimony}"
mkdir -p "$WORK"

# ---- phase 1: seed the typed inputs -----------------------------------------
if [ "$COMPARE_ONLY" = 0 ]; then
  mapfile -t SRCS < <(find "$CORPUS" -name '*.nim' | sort)
  echo "seeding ${#SRCS[@]} corpus sources into $WORK/nc (jobs=$JOBS)"
  # One worker gets a cold cache and warms the stdlib for the shared cache; the
  # rest then hit it. Seeding one file first avoids N workers each paying the
  # full system.nim lowering and racing to write the same entries.
  # $NIMFLAGS carries whatever the corpus needs to typecheck at all -- the `-p:`
  # search paths for a corpus that is a real project rather than free-standing
  # files (see tests/game.sh).
  # shellcheck disable=SC2086
  "$NIMONY" check --nimcache:"$WORK/nc" $NIMFLAGS "${SRCS[0]}" >/dev/null 2>&1
  printf '%s\n' "${SRCS[@]}" | \
    xargs -P "$JOBS" -I{} sh -c '"$0" check --nimcache:"$1" $2 "$3"' \
      "$NIMONY" "$WORK/nc" "$NIMFLAGS" {} >/dev/null 2>&1
fi

mapfile -t INPUTS < <(find "$WORK/nc" -name '*.s.nif' | sort)
[ "${#INPUTS[@]}" -gt 0 ] || { echo "differential: no .s.nif inputs were produced" >&2; exit 2; }

# ---- phase 2: lower each input with both, byte-compare ----------------------
# The flags mirror what nifmake actually invokes hexer with. `--isMain` changes
# the emitted tree (main-module init, app type), so both spellings are compared.
# The module hash in a `.s.nif` name says nothing to a human; its header carries
# the source path it came from. Report that instead.
srcOf() { head -c 400 "$1" | grep -o '[A-Za-z0-9_./-]*\.nim' | head -1; }

A="$WORK/ref"; B="$WORK/ours"
rm -rf "$A" "$B"; mkdir -p "$A" "$B"

pass=0; fail=0; skip=0; ahead=0
for s in "${INPUTS[@]}"; do
  base="$(basename "$s" .s.nif)"
  for mode in plain main; do
    extra=""
    [ "$mode" = main ] && extra="--isMain --app:console"
    "$REF"  c --bits:64 --cpu:le --flags:br $extra --outdir:"$A" "$s" >"$A/$base.log" 2>&1; ea=$?
    "$OURS" c --bits:64 --cpu:le --flags:br $extra --outdir:"$B" "$s" >"$B/$base.log" 2>&1; eb=$?

    # Three ways the exit codes can disagree, and only one of them is a defect.
    #   ref ok  / ours fails -> a regression in ours. FAIL.
    #   ref fails / ours ok  -> a bug FIXED here and not yet upstream. Report it
    #                           by name so the list stays honest and shrinks as
    #                           upstream catches up; it is not a failure.
    #   both fail            -> the reference cannot lower this input, so the
    #                           case constrains nothing. Counted, never hidden.
    if [ "$ea" = 0 ] && [ "$eb" != 0 ]; then
      fail=$((fail+1))
      echo "FAIL $base [$mode]: reference lowered it, we did not (exit $eb)"
      sed 's/^/    /' "$B/$base.log" | head -10
      continue
    fi
    if [ "$ea" != 0 ] && [ "$eb" = 0 ]; then
      ahead=$((ahead+1))
      echo "AHEAD $base [$mode] ($(srcOf "$s")): the reference aborts here, we lower it"
      continue
    fi
    if [ "$ea" != 0 ]; then skip=$((skip+1)); continue; fi

    bad=0
    for out in "$base.x.nif" "$base.dce.nif"; do
      if [ -f "$A/$out" ] || [ -f "$B/$out" ]; then
        cmp -s "$A/$out" "$B/$out" || { bad=1; echo "FAIL $base [$mode]: $out differs"
          diff -u "$A/$out" "$B/$out" 2>/dev/null | head -20 | sed 's/^/    /'; }
      fi
    done
    if [ "$bad" = 0 ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
  done
done

total=$((pass+fail+skip+ahead))
echo ""
echo "$pass/$total lowerings identical · $ahead ahead of the reference · $skip not lowerable by either · $fail FAILED"
[ "$fail" = 0 ] || exit 1
