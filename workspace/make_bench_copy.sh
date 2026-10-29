#!/usr/bin/env bash
# Make an independent bench copy (with build cache) for a parallel agent, reset to a snapshot.
# usage: make_bench_copy.sh <dest> <snapshot>
set -euo pipefail
dest=$1; snap=$2
[ -e "$dest" ] && { echo "exists: $dest"; exit 1; }
cp -a ~/shorecdlp "$dest"
cd "$dest"
rm -rf ShorECDLP/Submission/Entrant
cp -r /mnt/c/code/shor-ecdlp-contest/entrants/$snap/Entrant ShorECDLP/Submission/Entrant
git status --short --untracked-files=all | head
du -sh "$dest" | cut -f1
