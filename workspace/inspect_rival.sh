#!/usr/bin/env bash
cd /home/gitzard/shorecdlp-a
c=67e943d
git show --stat --format='%an %cs %s' $c | head -20
echo "== Entrant files:"; git ls-tree -r --name-only $c ShorECDLP/Submission/Entrant | head -40
echo "== bounds/rounds/acceptance:"; git grep -n -E 'streamingRounds|Rounds :=|independentRetrySuccessProbability|/1000\)|qubits :=|tModel :=|Bounds := ' $c -- ShorECDLP/Submission/Entrant | cut -c1-200 | head -20
echo "== header:"; git show $c:ShorECDLP/Submission/Entrant/Main.lean | head -30
