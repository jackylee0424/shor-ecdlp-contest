#!/usr/bin/env bash
set -euo pipefail

: "${BENCH:?set BENCH to the benchmark checkout}"

patch_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
entrant=ShorECDLP/Submission/Entrant
patch_file="$patch_dir/src/lookup-trees.patch"
targets=(
  "$entrant/Main.lean"
  "$entrant/Single/Fourier.lean"
  "$entrant/Single/Physical.lean"
)

for target in "${targets[@]}"; do
  git -C "$BENCH" ls-files --error-unmatch "$target" >/dev/null
done

# A second worktree application is a successful no-op. If the reverse patch
# applies to clean tracked files, the leader itself has absorbed the change.
if git -C "$BENCH" apply --reverse --check "$patch_file" 2>/dev/null; then
  dirty=false
  for target in "${targets[@]}"; do
    if ! git -C "$BENCH" diff --quiet -- "$target"; then
      dirty=true
    fi
  done
  if "$dirty"; then
    echo "20-lookup-trees already applied"
    exit 0
  fi
  echo "20-lookup-trees absorbed by leader" >&2
  exit 3
fi

# A leader with its own specialized tree has absorbed or superseded this patch.
if grep -q 'namespace ShorECDLP.Entrant.Lookup15Scratch' \
    "$BENCH/$entrant/Single/Physical.lean"; then
  echo "20-lookup-trees absorbed or superseded by leader" >&2
  exit 3
fi

if ! git -C "$BENCH" apply --check "$patch_file"; then
  echo "20-lookup-trees is not applicable to this leader" >&2
  exit 3
fi

git -C "$BENCH" apply "$patch_file"
echo "applied 20-lookup-trees"
