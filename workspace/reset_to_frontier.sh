#!/usr/bin/env bash
set -euo pipefail
cd /home/gitzard/shorecdlp
git fetch -q origin
git reset -q --hard origin/master
git clean -fdq -- ShorECDLP/Submission/Entrant
git log --oneline -1
git status --short | wc -l
ls ShorECDLP/Submission/Entrant ShorECDLP/Submission/Entrant/Streaming
