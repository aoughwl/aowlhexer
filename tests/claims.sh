#!/usr/bin/env bash
# tests/claims.sh — do the NUMBERS in README.md still agree with the gates?
#
# The other two scripts here compare lowered .c.aif against nimony's hexer. This
# one checks the PROSE, which had no gate at all. See CLAIMS.tsv for the rows and
# tools/claimcheck.py for the argument; the short version is that three repos in
# this toolchain were caught in two days publishing a score no gate had printed.
#
#   bash tests/claims.sh          # cheap
#   bash tests/claims.sh --all    # also tests/differential.sh --compare-only
#   bash tests/claims.sh --sweep  # numbers with no row in CLAIMS.tsv
#
# It is RED today and should be. README's "Verified" section states
# `fib(20)=6765`, `ack(3,4)=125`, `fib(25)=75025` as a property of the pipeline,
# and neither gate here ever runs a produced binary — both stop at the byte
# comparison of the lowering. A number whose producer does not exist is the
# exact shape of the defect this file exists to catch, so it fails until someone
# writes the script or restates the claim as aifmony's, naming aifmony's command.
#
# It never rewrites a document. Exit 0 clean / 1 disagreement or unattributed /
# 2 could not be checked.
set -uo pipefail
cd "$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 tools/claimcheck.py --label aowlhexer "$@"
