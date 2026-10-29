#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
for f in Arithmetic/PointCorrection.lean; do git show $R:ShorECDLP/Submission/2607_13816/$f | grep -n -B3 -A10 "def fig14EncodedEquiv\|def finiteMatchingSwaps\|def finiteMatchingPermutation\|def protectedExceptionPairs\|def fig14ExceptionalPoints"; done
git grep -n "def protectedExceptionPairs\|def exceptionalEndpointWords\|def fig14EncodedEquiv" $R -- ShorECDLP | head
