#!/usr/bin/env bash
for p in $(pgrep -f '^codex exec'); do kill "$p"; done
sleep 2; pgrep -af '^codex exec' || echo "codex agents stopped"
ts=$(date +%Y%m%d-%H%M)
d=/mnt/c/code/shor-ecdlp-contest/entrants/$ts-wip-brief12
mkdir -p "$d" && cp -r ~/shorecdlp/ShorECDLP/Submission/Entrant "$d/Entrant" && printf 'name: wip-brief12\nnote: Block-E rewrite on 6-round base; stopped when baseline moved to single-trial\n' > "$d/META.txt" && echo "saved $d"
