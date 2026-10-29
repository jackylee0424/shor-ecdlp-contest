#!/usr/bin/env bash
set -euo pipefail
cd ~/shorecdlp
echo "== protected diff HEAD..origin/master (excluding Entrant):"
git diff --stat HEAD origin/master -- . ':!ShorECDLP/Submission/Entrant' | tail -3
echo "== brief-03 leftovers:"; ls ShorECDLP/Submission/Entrant/Streaming 2>/dev/null || true
if [ -d ShorECDLP/Submission/Entrant/Streaming ]; then
  /mnt/c/code/shor-ecdlp-contest/formal-tools/snapshot.sh brief03-partial "brief 03 partial Streaming/ (Costs.lean failed omega); superseded by upstream port"
  rm -rf ShorECDLP/Submission/Entrant/Streaming .lake/build/lib/lean/ShorECDLP/Submission/Entrant/Streaming .lake/build/ir/ShorECDLP/Submission/Entrant/Streaming
fi
git status --short
python3 - <<'PY'
r=26; p=0.163
print("success 26 rounds:", 1-(1-p)**r, "min rounds:", next(k for k in range(1,100) if 1-(1-p)**k>=0.99))
t56,m56=806028979896,48194018992
print("per-round T", t56/56, "per-round M", m56/56)
t=t56//56*r; m=m56//56*r
print("T",t,"M",m,"QxT",3932*t)
PY
