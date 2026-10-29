#!/usr/bin/env bash
# Run the official local benchmark (same as `yukon run --track lean`, minus trace sync)
# and print the resulting metrics plus the Q×T score.
# usage: score.sh [--yukon]    (--yukon runs `yukon run --track lean` instead)
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$BENCH"
log="$LOGS/score-$(date +%Y%m%d-%H%M%S).log"
echo "scoring (log: $log)"
set +e
if [[ "${1:-}" == "--yukon" ]]; then
  yukon run --track lean >"$log" 2>&1
else
  ./benchmark.sh >"$log" 2>&1
fi
rc=$?
set -e
tail -n 25 "$log"
if [[ -f scripts/score.json ]]; then
  python3 - scripts/score.json <<'PY'
import json, sys
s = json.load(open(sys.argv[1]))
print(json.dumps(s, indent=2)[:4000])
def find(d, *keys):
    for k in keys:
        if isinstance(d, dict) and k in d: return d[k]
    if isinstance(d, dict):
        for v in d.values():
            r = find(v, *keys)
            if r is not None: return r
    return None
q = find(s, "qubits", "logicalQubits")
t = find(s, "tModel", "tModelCount", "t_model")
if isinstance(q, int) and isinstance(t, int):
    print(f"\nQxT = {q:,} x {t:,} = {q*t:,}")
PY
fi
echo "rc=$rc"
exit "$rc"
