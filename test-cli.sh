#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake exe graphfold_tests
expected_shortest=$'0: 0\n1: 2\n2: 5\n3: 3'
expected_paths=$'0: 1\n1: 1\n2: 2\n3: 3'
expected_optimal=$'0: min=0,count=1\n1: min=2,count=1\n2: min=5,count=2\n3: min=3,count=1'
[[ "$(lake exe shortest examples/diamond.txt)" == "$expected_shortest" ]]
[[ "$(lake exe paths examples/diamond.txt)" == "$expected_paths" ]]
[[ "$(lake exe optimal examples/diamond.txt)" == "$expected_optimal" ]]
[[ "$(lake exe optimal examples/tied-optima.txt)" == $'0: min=0,count=1\n1: min=2,count=1\n2: min=1,count=1\n3: min=5,count=2' ]]
[[ "$(lake exe shortest examples/unreachable.txt)" == $'0: 0\n1: 7\n2: INF' ]]
[[ "$(lake exe paths examples/unreachable.txt)" == $'0: 1\n1: 1\n2: 0' ]]
[[ "$(lake exe optimal examples/unreachable.txt)" == $'0: min=0,count=1\n1: min=7,count=1\n2: INF,count=0' ]]
[[ "$(lake exe shortest examples/weighted-branch.txt)" == $'0: 0\n1: 100\n2: 1\n3: 2' ]]
[[ "$(lake exe paths examples/weighted-branch.txt)" == $'0: 1\n1: 1\n2: 1\n3: 2' ]]
if lake exe shortest examples/cycle-invalid.txt >/dev/null 2>&1; then
  echo "Cycle input was not rejected" >&2; exit 1
fi
if lake exe optimal examples/cycle-invalid.txt >/dev/null 2>&1; then
  echo "Cycle input was not rejected by optimal" >&2; exit 1
fi
if lake exe paths examples/cycle-invalid.txt >/dev/null 2>&1; then
  echo "Cycle input was not rejected by paths" >&2; exit 1
fi
echo "CLI integration tests passed"
