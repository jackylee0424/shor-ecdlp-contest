#!/usr/bin/env bash
set -euo pipefail

: "${BENCH:?set BENCH to the benchmark checkout}"
git -C "$BENCH" rev-parse --is-inside-work-tree >/dev/null

echo "21-right208 is parked: no finite-kernel Lean proof clears 99%" >&2
exit 3
