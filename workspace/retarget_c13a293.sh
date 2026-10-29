#!/usr/bin/env bash
for p in $(pgrep -f '^codex exec'); do kill "$p"; done
pkill -f 'formal-tools/restack.sh' ; pkill -f 'lake build' ; sleep 3
pgrep -af '^codex exec|restack.sh' || echo "stopped agents and restack"
bash /mnt/c/code/shor-ecdlp-contest/workspace/rebase_all.sh c13a293
