#!/usr/bin/env bash
# Independent check of the latest official score receipt and entrant hygiene.
cd /mnt/c/code/shor-ecdlp-contest
log=$(ls -t logs/score-*.log | head -1); echo "log: $log"
grep -E '"accepted"|Verified score|replay passed|axioms' "$log" | tail -6
cat ~/shorecdlp/scripts/score.json
cd ~/shorecdlp
echo "== forbidden tokens in Entrant:"; grep -rnE '\b(sorry|admit|native_decide|bv_decide|axiom|opaque|unsafe|partial)\b|skipKernelTC|implemented_by' ShorECDLP/Submission/Entrant | grep -v -- '--' | head
echo "== rounds/bound in Entrant:"; grep -rnE '546/1000|streamingRounds|independentRetrySuccessProbability' ShorECDLP/Submission/Entrant | head -6
/mnt/c/code/shor-ecdlp-contest/formal-tools/boundary.sh | head -12
