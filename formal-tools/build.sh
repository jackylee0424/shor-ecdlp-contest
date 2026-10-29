#!/usr/bin/env bash
# Build Lean modules in the benchmark checkout (default: the entrant root module).
# usage: build.sh [Module.Name ...]
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$BENCH"
targets=("${@:-ShorECDLP.Submission.Entrant.Main}")
log="$LOGS/build-$(date +%Y%m%d-%H%M%S).log"
echo "building ${targets[*]} (log: $log)"
start=$(date +%s)
set +e
lake build "${targets[@]}" 2>&1 | tee "$log" | grep -E "error|warning: declaration uses 'sorry'|^✖|Build completed|^error"
rc=${PIPESTATUS[0]}
set -e
echo "rc=$rc elapsed=$(( $(date +%s) - start ))s"
exit "$rc"
