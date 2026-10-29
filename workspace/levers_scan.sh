#!/usr/bin/env bash
cd ~/shorecdlp
U=upstream/lamport/challenge-final-certificate
echo "== qubit bound / reset list"
git grep -n -E "3932|3931|resetList|batchedReset|qubits_le" $U -- 'ShorECDLP/Submission/2607_13816/Challenge/*.lean' | cut -c1-220 | head -25
echo "== per-round acceptance constants"
git grep -n -E "163|wrappedIdeal_mass_lower" $U -- 'ShorECDLP/Submission/2607_13816/**/*.lean' | cut -c1-200 | head -15
echo "== T per window"
git grep -n -E "windowCost|14393374641|UniformT|tModel_le" $U -- 'ShorECDLP/Submission/2607_13816/Challenge/*.lean' | cut -c1-200 | head -20
echo "== progress of brief 04"; ls ShorECDLP/Submission/Entrant/; ls ShorECDLP/Submission/Entrant/Streaming 2>/dev/null | head; tail -c 600 /mnt/c/code/shor-ecdlp-contest/logs/codex-04.log
