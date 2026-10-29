#!/bin/bash
cd ~/shorecdlp
for f in Model Bounds Windows; do
 echo "=== $f"; git show origin/master:ShorECDLP/Submission/2607_13816/EEA/$f.lean | grep -E '^/--|^  [A-Z].*-/$|^-- |^(def|theorem) ' | head -40
done
