#!/usr/bin/env bash
cd /home/gitzard/shorecdlp-a
for c in a75553f 8513c15; do
  echo "######## $c"; git show --stat --format='%an %s' $c | tail -8
  git show $c:ShorECDLP/Submission/Entrant/Main.lean | sed -n '1,45p'
  git grep -n -E 'Bounds := ⟨|repeat [0-9]+ 0|independentRetrySuccessProbability \(' $c -- ShorECDLP/Submission/Entrant | cut -c1-180 | head -8
done
cd ~/shorecdlp-a && for s in 8c5e543 3e53f42; do echo "######## note $s"; yukon submission-note $s 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | head -60; done
