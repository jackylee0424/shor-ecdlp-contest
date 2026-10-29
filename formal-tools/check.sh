#!/usr/bin/env bash
# Elaborate one Lean file against the built benchmark library, without writing oleans.
# Works for entrant files and for scratch files under workspace/.
# usage: check.sh path/to/File.lean   (absolute, or relative to the lab or the benchmark)
set -euo pipefail
source "$(dirname "$0")/env.sh"
[[ $# -eq 1 ]] || die "usage: check.sh FILE.lean"
f="$1"
if [[ "$f" != /* ]]; then
  if [[ -f "$PWD/$f" ]]; then f="$PWD/$f"
  elif [[ -f "$LAB/$f" ]]; then f="$LAB/$f"
  elif [[ -f "$BENCH/$f" ]]; then f="$BENCH/$f"
  else die "no such file: $1"; fi
fi
cd "$BENCH"
start=$(date +%s)
set +e
lake env lean "$f"
rc=$?
set -e
echo "rc=$rc elapsed=$(( $(date +%s) - start ))s"
exit "$rc"
