#!/usr/bin/env bash
# Compare protected trees between the bench frontier and an upstream VerifiedQC ref.
set -euo pipefail
cd ~/shorecdlp
git remote get-url upstream >/dev/null 2>&1 || git remote add upstream /mnt/c/code/ShorECDLP
git fetch -q upstream 'refs/remotes/origin/*:refs/remotes/upstream/*'
U=${1:-upstream/lamport/challenge-final-certificate}
for p in ShorECDLP/Challenge ShorECDLP/Judge ShorECDLP/Framework ShorECDLP/Math ShorECDLP/Submission/Naive ShorECDLP/Submission/2607_13816 lakefile.lean lean-toolchain lake-manifest.json scripts; do
  a=$(git rev-parse "origin/master:$p" | cut -c1-10); b=$(git rev-parse "$U:$p" | cut -c1-10)
  printf '%-40s bench=%s upstream=%s %s\n' "$p" "$a" "$b" "$([ "$a" = "$b" ] && echo SAME || echo DIFF)"
done
echo "merge-base: $(git merge-base origin/master "$U" | cut -c1-10)"
git diff --stat origin/master "$U" -- ShorECDLP/Challenge ShorECDLP/Judge ShorECDLP/Framework ShorECDLP/Math scripts lakefile.lean | tail -8
