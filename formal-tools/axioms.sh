#!/usr/bin/env bash
# Print the axioms the entrant certificate depends on. Allowed: propext, Classical.choice, Quot.sound.
# usage: axioms.sh [Decl.Name]   (default ShorECDLP.Entrant.certificate)
set -euo pipefail
source "$(dirname "$0")/env.sh"
decl="${1:-ShorECDLP.Entrant.certificate}"
tmp="$(mktemp --suffix=.lean)"
trap 'rm -f "$tmp"' EXIT
printf 'import ShorECDLP.Submission.Entrant.Main\n#print axioms %s\n' "$decl" > "$tmp"
cd "$BENCH"
lake env lean "$tmp"
