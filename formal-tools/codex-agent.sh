#!/usr/bin/env bash
# Launch a Codex CLI sub-agent (gpt-6.1-sol) inside WSL with the lab as cwd and the
# benchmark checkout as an extra writable root. Sandbox: workspace-write (Linux bwrap).
# usage: codex-agent.sh BRIEF.md [LOGFILE]
# CODEX_HOME defaults to ~/.codex-wsl (config.toml + auth.json symlink; see docs/ENVIRONMENT.md).
set -euo pipefail
source "$(dirname "$0")/env.sh"
[[ $# -ge 1 && -f "$1" ]] || die "usage: codex-agent.sh BRIEF.md [LOG]"
brief="$1"
log="${2:-$LOGS/codex-$(basename "$brief" .md)-$(date +%Y%m%d-%H%M%S).log}"
export CODEX_HOME="${CODEX_HOME:-$HOME/.codex-wsl}"
echo "codex agent: brief=$brief log=$log"
codex exec --skip-git-repo-check \
  -m "${CODEX_MODEL:-gpt-6.1-sol}" \
  -C "$LAB" --add-dir "$BENCH" \
  - < "$brief" > "$log" 2>&1
rc=$?
echo "rc=$rc"; tail -n 40 "$log"
exit "$rc"
