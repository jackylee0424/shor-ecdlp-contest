#!/usr/bin/env bash
cd ~/shorecdlp-a
for s in "$@"; do echo "######## $s"; yukon submission-note "$s" 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | sed -n '1,34p'; done
