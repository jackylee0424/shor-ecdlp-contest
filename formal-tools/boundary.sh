#!/usr/bin/env bash
# Fail if anything outside ShorECDLP/Submission/Entrant differs from the pinned commit.
# The official checker also rejects untracked AND ignored files (except the build dir),
# so never leave notes, scratch files or symlinks in the benchmark checkout.
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$BENCH"
bad=$(git status --porcelain --ignored --untracked-files=all \
  | grep -v -E '^.. (ShorECDLP/Submission/Entrant/|\.lake/|scripts/score\.json$|__pycache__/|.*/__pycache__/)' || true)
if [[ -n "$bad" ]]; then
  echo "BOUNDARY VIOLATION (outside Entrant):"
  echo "$bad"
  exit 1
fi
if find ShorECDLP/Submission/Entrant -type l | grep -q .; then
  echo "BOUNDARY VIOLATION: symlink inside Entrant"; exit 1
fi
echo "boundary ok; entrant changes:"
git status --porcelain --untracked-files=all -- ShorECDLP/Submission/Entrant || true
