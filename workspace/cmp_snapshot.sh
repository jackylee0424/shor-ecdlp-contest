#!/usr/bin/env bash
# Compare bench Entrant against a lab snapshot. usage: cmp_snapshot.sh <snapshot-dir-name>
snap=/mnt/c/code/shor-ecdlp-contest/entrants/$1/Entrant
cd ~/shorecdlp/ShorECDLP/Submission/Entrant
for f in *.lean; do cmp -s "$f" "$snap/$f" && echo "$f same" || echo "$f DIFFERS"; done
ls "$snap"
