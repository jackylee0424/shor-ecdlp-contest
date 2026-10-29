#!/usr/bin/env bash
set -euo pipefail
cd ~/shorecdlp
U=${1:-upstream/lamport/challenge-final-certificate}
echo "== Challenge diff stat"; git diff --stat origin/master "$U" -- ShorECDLP/Challenge
echo "== Challenge diff (head)"; git diff origin/master "$U" -- ShorECDLP/Challenge | head -60
echo "== 2607 status counts"; git diff --name-status origin/master "$U" -- ShorECDLP/Submission/2607_13816 | cut -f1 | sort | uniq -c
echo "== 2607 modified (not added)"; git diff --name-status origin/master "$U" -- ShorECDLP/Submission/2607_13816 | grep -v '^A' | head -20
echo "== forbidden tokens in added 2607 files"
git diff --name-only --diff-filter=A origin/master "$U" -- 'ShorECDLP/Submission/2607_13816/*.lean' | while read f; do git show "$U:$f" | grep -nE '\b(native_decide|bv_decide|sorry|admit|opaque|unsafe|partial|axiom)\b|implemented_by|@\[extern|skipKernelTC' | sed "s#^#$f:#"; done | head
