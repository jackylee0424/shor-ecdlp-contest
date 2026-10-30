#!/usr/bin/env bash
for p in $(pgrep -f '^codex exec'); do
  cmd=$(tr '\0' ' ' < /proc/$p/cmdline)
  case "$cmd" in *"--add-dir /home/gitzard/shorecdlp-c"*) kill $p; echo "stopped brief28 ($p)";; *) echo "kept ${cmd:0:80}";; esac
done
ls /mnt/c/code/shor-ecdlp-contest/workspace | grep -i -E 'hull|DivstepBound2' || true
