#!/bin/bash
cd ~/shorecdlp
R=upstream/lamport/challenge-final-certificate
git show $R:ShorECDLP/Submission/2607_13816/Challenge/ExceptionalFields.lean | sed -n 1,80p
git show $R:ShorECDLP/Submission/2607_13816/Challenge/EndpointLoad.lean | sed -n 95,129p
