#!/bin/bash
cd ~/shorecdlp
git ls-tree -r --name-only origin/master ShorECDLP/Submission/2607_13816/Arithmetic | head -80
for f in InPlacePrimitiveCounts HornerInverse SquareInverse; do
  echo "=== $f"; git show origin/master:ShorECDLP/Submission/2607_13816/Arithmetic/$f.lean 2>/dev/null | grep -n -E '^(theorem|lemma|def|/--|--)|[0-9]{5,}' | head -60
done
