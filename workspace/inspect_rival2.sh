#!/usr/bin/env bash
cd /home/gitzard/shorecdlp-a
git fetch -q origin
c=93051d2
git show --stat --format='%an %cs %s' $c | tail -12
git ls-tree -r --name-only $c ShorECDLP/Submission/Entrant
echo "== Main header"; git show $c:ShorECDLP/Submission/Entrant/Main.lean | head -40
echo "== bounds"; git grep -n -E 'Bounds := ⟨|streamingRounds|/1000\)|/50\)|independentRetrySuccessProbability \(' $c -- ShorECDLP/Submission/Entrant | cut -c1-200 | head -10
