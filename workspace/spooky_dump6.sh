#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
git grep -n -A25 "def unaryAction " $R -- ShorECDLP | head -50
git grep -n "theorem unaryAction.*run\|theorem unaryAction_classical\|theorem unaryAction_" $R -- ShorECDLP | head
git show $R:ShorECDLP/Submission/2607_13816/Challenge/WindowBody.lean | sed -n 1,103p
