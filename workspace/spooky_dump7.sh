#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
git show $R:ShorECDLP/Submission/2607_13816/EEA/UnaryAction.lean > /mnt/c/code/shor-ecdlp-contest/workspace/spooky_src/UnaryAction.lean
git show $R:ShorECDLP/Submission/2607_13816/Challenge/BatchExecution.lean | sed -n 100,165p
