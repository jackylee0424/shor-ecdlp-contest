#!/usr/bin/env bash
# Save the current Entrant tree into the lab (entrants/<date>-<name>/), with metadata
# and the last score.json if present. Snapshots are how work survives across agents.
# usage: snapshot.sh <short-name> [note...]
set -euo pipefail
source "$(dirname "$0")/env.sh"
[[ $# -ge 1 ]] || die "usage: snapshot.sh NAME [note]"
name="$1"; shift
dest="$SNAPSHOTS/$(date +%Y%m%d-%H%M)-$name"
mkdir -p "$dest"
cp -r "$ENTRANT" "$dest/Entrant"
[[ -f "$BENCH/scripts/score.json" ]] && cp "$BENCH/scripts/score.json" "$dest/score.json"
{
  echo "name: $name"
  echo "date: $(date -Is)"
  echo "bench_commit: $(git -C "$BENCH" rev-parse HEAD)"
  echo "note: ${*:-}"
} > "$dest/META.txt"
echo "snapshot -> $dest"
