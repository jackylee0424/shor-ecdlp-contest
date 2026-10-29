#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
git grep -n "def oddCoefficient" -A6 $R -- ShorECDLP | head -12
echo ----PRIME
git grep -n -E "theorem [A-Za-z_]*(prime|Prime|order|Order)[A-Za-z_]*" $R -- ShorECDLP/Challenge ShorECDLP/Math ShorECDLP/Framework ShorECDLP/Judge | head -40
echo ----NS
git grep -n -E "(addOrderOf|nsmul_eq_zero|IsOfFinAddOrder|Nat.Prime order|order\.Prime|Fact \(Nat.Prime order)" $R -- ShorECDLP | head -20
