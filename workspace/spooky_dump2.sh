#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
git show $R:ShorECDLP/Submission/2607_13816/Arithmetic/PointCorrection.lean | grep -n -B2 -A12 "def finiteMatchingSwaps\|def finiteMatchingPermutation\|def runFiniteSwaps"
grep -n "theorem\|def " ShorECDLP/Framework/Quantum/MeasurementUncompute.lean | head -60
