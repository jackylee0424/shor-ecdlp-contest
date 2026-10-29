#!/usr/bin/env bash
set -euo pipefail

: "${BENCH:?set BENCH to the benchmark checkout}"
entrant="$BENCH/ShorECDLP/Submission/Entrant"

test ! -e "$entrant/Compiler.lean"
rg -q 'Merged public-work provenance' "$entrant/Main.lean"
rg -q 'noncomputable def entry : StraightEntry := lowerEntry 1024 Parent.entry' "$entrant/Main.lean"
rg -q 'def bounds : Bounds := ⟨856, 11513899424, 8551122464⟩' "$entrant/Main.lean"
echo "stack/10-temp-and-compiler: present"

