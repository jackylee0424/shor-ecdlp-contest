#!/usr/bin/env bash
# Rebuild our stack of patches (stack/NN-*/apply.sh) on top of a leader commit, score it, and report
# the cut vs the leader and the >10 % submission verdict.
# usage: restack.sh [leader-commit]   (BENCH defaults to ~/shorecdlp-c; leader defaults to origin/master tip)
set -uo pipefail
export BENCH="${BENCH:-$HOME/shorecdlp-c}"
source "$(dirname "$0")/env.sh"
cd "$BENCH"
git fetch -q origin
leader="${1:-$(git rev-parse --short origin/master)}"
git reset -q --hard "$leader" && git clean -fdq -- ShorECDLP/Submission/Entrant
ts=$(date +%Y%m%d-%H%M%S)
report="$LOGS/restack-$ts.md"
{
  echo "# restack $ts"
  echo "- bench: $BENCH"
  echo "- leader commit: $leader ($(git log -1 --format=%s "$leader"))"
} > "$report"

# leader score: build + score the untouched leader first (cached builds make this cheap)
"$LAB/formal-tools/score.sh" > "$LOGS/restack-$ts-leader.log" 2>&1
leader_score=$(python3 -c 'import json;print(json.load(open("scripts/score.json"))["scoreExact"])' 2>/dev/null || echo "?")
echo "- leader score (local): $leader_score" >> "$report"

applied=()
for p in $(ls -d "$LAB"/stack/[0-9][0-9]-* 2>/dev/null | sort); do
  name=$(basename "$p")
  [[ -f "$p/ENABLED" ]] || { echo "- $name: parked" >> "$report"; continue; }
  set +e; BENCH="$BENCH" LAB="$LAB" bash "$p/apply.sh" > "$LOGS/restack-$ts-$name.log" 2>&1; rc=$?; set -e 2>/dev/null; set +e
  case $rc in
    0) applied+=("$name"); echo "- $name: applied" >> "$report" ;;
    3) echo "- $name: SKIPPED (not applicable / absorbed by leader; see log)" >> "$report" ;;
    *) echo "- $name: BROKEN (rc=$rc; see logs/restack-$ts-$name.log). Stack stopped here." >> "$report"; break ;;
  esac
done

if [[ ${#applied[@]} -eq 0 ]]; then
  echo "- result: nothing applied; stack == leader" >> "$report"; cat "$report"; exit 0
fi
"$LAB/formal-tools/boundary.sh" >> "$LOGS/restack-$ts-boundary.log" 2>&1 || echo "- boundary: FAILED" >> "$report"
"$LAB/formal-tools/score.sh" > "$LOGS/restack-$ts-stack.log" 2>&1
stack_score=$(python3 -c 'import json;print(json.load(open("scripts/score.json"))["scoreExact"])' 2>/dev/null || echo "?")
python3 - "$leader_score" "$stack_score" >> "$report" <<'PY'
import sys
l, s = sys.argv[1], sys.argv[2]
if l.isdigit() and s.isdigit():
    l, s = int(l), int(s)
    cut = (l - s) / l * 100
    print(f"- stack score: {s:,}  (leader {l:,})")
    print(f"- cut vs leader: {cut:.4f} %  -> submission bar (>10 %): {'MET' if cut > 10 else 'not met'}")
else:
    print(f"- stack score: {s} (scoring failed? see logs)")
PY
cat "$report"
