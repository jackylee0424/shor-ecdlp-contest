#!/usr/bin/env bash
# Replace the benchmark Entrant tree with a lab snapshot (or `baseline` for the pinned one).
# Refuses if the current Entrant has changes that are not snapshotted, unless --force.
# usage: restore.sh <entrants/DIR | baseline> [--force]
set -euo pipefail
source "$(dirname "$0")/env.sh"
[[ $# -ge 1 ]] || die "usage: restore.sh SNAPSHOT_DIR|baseline [--force]"
src="$1"; force="${2:-}"
if [[ "$force" != "--force" ]] && [[ -n "$(git -C "$BENCH" status --porcelain -- ShorECDLP/Submission/Entrant)" ]]; then
  matched=0
  for d in "$SNAPSHOTS"/*/Entrant; do
    diff -rq "$d" "$ENTRANT" >/dev/null 2>&1 && matched=1 && break
  done
  [[ $matched -eq 1 ]] || die "current Entrant has unsnapshotted changes; run snapshot.sh first or pass --force"
fi
if [[ "$src" == "baseline" ]]; then
  git -C "$BENCH" checkout -- ShorECDLP/Submission/Entrant
  git -C "$BENCH" clean -fdq -- ShorECDLP/Submission/Entrant
else
  [[ -d "$src" ]] || src="$SNAPSHOTS/$src"
  [[ -d "$src/Entrant" ]] || die "no Entrant/ in $src"
  rm -rf "$ENTRANT"
  cp -r "$src/Entrant" "$ENTRANT"
fi
echo "restored Entrant from $src"
