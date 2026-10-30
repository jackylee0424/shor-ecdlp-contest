#!/usr/bin/env bash
for pat in 'add-dir /home/gitzard/shorecdlp-m' 'add-dir /home/gitzard/shorecdlp$' 'add-dir /home/gitzard/shorecdlp -'; do :; done
for p in $(pgrep -f '^codex exec'); do
  cmd=$(tr '\0' ' ' < /proc/$p/cmdline)
  case "$cmd" in
    *"--add-dir /home/gitzard/shorecdlp-m "*|*"--add-dir /home/gitzard/shorecdlp-m") kill $p; echo "stopped brief17 ($p)";;
    *"--add-dir /home/gitzard/shorecdlp "*|*"--add-dir /home/gitzard/shorecdlp") kill $p; echo "stopped brief19 ($p)";;
    *) echo "kept: ${cmd:0:120}";;
  esac
done
ts=$(date +%Y%m%d-%H%M)
for b in shorecdlp-m:brief17 shorecdlp:brief19; do
  d=/mnt/c/code/shor-ecdlp-contest/entrants/$ts-wip-${b#*:}; mkdir -p $d; cp -r /home/gitzard/${b%%:*}/ShorECDLP/Submission/Entrant $d/Entrant; echo "saved $d"
done
