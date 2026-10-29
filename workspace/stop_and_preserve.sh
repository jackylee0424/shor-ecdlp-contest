#!/usr/bin/env bash
set -u
for p in $(pgrep -f '^codex exec'); do kill $p; done
sleep 3; pgrep -af '^codex exec' || echo "codex agents stopped"
lab=/mnt/c/code/shor-ecdlp-contest
ts=$(date +%Y%m%d-%H%M)
for b in shorecdlp shorecdlp-c; do
  d=$lab/entrants/$ts-wip-$b
  mkdir -p $d && cp -r /home/gitzard/$b/ShorECDLP/Submission/Entrant $d/Entrant
  echo "name: wip-$b\nnote: stopped mid-build (frontier moved to 855q ff1bf8d)" > $d/META.txt
  echo "preserved $b -> $d ($(find $d -name '*.lean' | wc -l) lean files)"
done
