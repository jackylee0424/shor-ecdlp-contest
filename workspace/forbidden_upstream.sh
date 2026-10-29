#!/usr/bin/env bash
cd ~/shorecdlp
U=${1:-upstream/lamport/challenge-final-certificate}
git diff --name-only --diff-filter=A origin/master "$U" -- 'ShorECDLP/Submission/2607_13816/*.lean' > /tmp/added.txt
echo "added lean files: $(wc -l < /tmp/added.txt); total lines: $(while read f; do git show "$U:$f"; done < /tmp/added.txt | wc -l)"
while read f; do git show "$U:$f" | grep -nE '\b(native_decide|bv_decide|sorry|admit|opaque|unsafe|partial|axiom|decide \+native)\b|implemented_by|@\[extern|skipKernelTC|maxHeartbeats 0' | sed "s#^#$f:#"; done < /tmp/added.txt | head -20
echo "--- repeat-count literals (56) in added files:"; while read f; do git show "$U:$f" | grep -c '\b56\b' | sed "s#^#$f: #"; done < /tmp/added.txt | grep -v ': 0$' | head -20
