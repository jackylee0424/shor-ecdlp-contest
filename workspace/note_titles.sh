#!/usr/bin/env bash
cd ~/shorecdlp-a
for s in "$@"; do
  t=$(yukon submission-note "$s" 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | grep -m1 '^# ' )
  echo "$s | $t"
done
