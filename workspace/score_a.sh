#!/usr/bin/env bash
set -euo pipefail
cd /home/gitzard/shorecdlp-a
snap=/mnt/c/code/shor-ecdlp-contest/entrants/20261029-1215-rounds6/Entrant
for f in Main Trial Success WindowMass; do cmp -s ShorECDLP/Submission/Entrant/$f.lean $snap/$f.lean && echo "$f same" || echo "$f DIFFERS"; done
echo "untracked/other entrant files:"; find ShorECDLP/Submission/Entrant -type f | grep -v -E '/(Main|Trial|Success|WindowMass)\.lean$' || echo none
git stash list | head -3
BENCH=/home/gitzard/shorecdlp-a /mnt/c/code/shor-ecdlp-contest/formal-tools/boundary.sh | head -3
BENCH=/home/gitzard/shorecdlp-a /mnt/c/code/shor-ecdlp-contest/formal-tools/score.sh 2>&1 | grep -E 'Verified score|accepted|replay passed|rc=' | tail -6
