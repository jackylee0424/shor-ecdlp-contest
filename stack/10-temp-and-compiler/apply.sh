#!/usr/bin/env bash
set -euo pipefail

: "${BENCH:?set BENCH to the benchmark checkout}"
entrant="$BENCH/ShorECDLP/Submission/Entrant"
here="$(cd "$(dirname "$0")" && pwd)"

if [[ -f "$entrant/Compiler.lean" ]] ||
   rg -q 'namespace ShorECDLP\.Entrant\.AndGadget|lowerEntry 1024 Parent\.entry' "$entrant/Main.lean"; then
  echo "stack/10-temp-and-compiler: compiler already present; absorbed by base"
  exit 3
fi

cd "$entrant"
if ! sha256sum -c --status <<'HASHES'
27eedc556cfc48c10c2542db752fbe1fecfbee9664a1c9ef7de36864885f71ce  Main.lean
7272e514db8132938cb6ceb64a9d9efcb546e053cf46e753ebb5e7b7b338df46  Single/Fourier.lean
54a023c31540b68cf81e348995ca45266763913ff0e79e22834af5679855c6f5  Single/Physical.lean
5aaf5e2ec2e6a8df607433836f4abca7fcfdde505f6ea5635c1e44e764c2e9de  Streaming/Resources.lean
9434de60e2e9fe6f49e9da9ba2b64e3294cf041c1e1b5c146de0b714c8411e47  Streaming/Semantics.lean
HASHES
then
  echo "stack/10-temp-and-compiler: expected exact spariev a72f4af Entrant base" >&2
  exit 1
fi

install -m 0644 "$here/src/Main.lean" "$entrant/Main.lean"
echo "stack/10-temp-and-compiler: applied to spariev a72f4af base"

