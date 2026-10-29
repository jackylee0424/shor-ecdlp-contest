#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
O=/mnt/c/code/shor-ecdlp-contest/workspace/spooky_src
for f in BatchExecution BatchedWindowCoherent BatchedWindowState WindowValidity CrossWindowPoint SharedTable Coefficients Coefficient PointTable ActualWindow BatchBoundary PlacedBatch; do
  git show $R:ShorECDLP/Submission/2607_13816/Challenge/$f.lean > $O/$f.lean 2>/dev/null
done
git grep -n "normalizedEndpointWords" $R -- ShorECDLP | grep "def \|theorem" | head
git grep -n -i "prime\b\|order_prime\|addOrderOf\|nsmul_eq_zero\|orderOf" $R -- ShorECDLP/Secp256k1* ShorECDLP/Challenge ShorECDLP/Framework | grep "theorem\|lemma\|def \|axiom" | head -30
ls ShorECDLP
