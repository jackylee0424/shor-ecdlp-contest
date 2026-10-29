# stack — our contributions as re-appliable patches over whatever the leader is

Each lever we contribute lives here as `stack/<NN>-<slug>/`, applied in `NN` order on top of the current leader's Entrant:

```
stack/<NN>-<slug>/
  apply.sh       # idempotent; edits only $BENCH/ShorECDLP/Submission/Entrant; exits 0 = applied,
                 # 3 = "not applicable / absorbed by leader" (skip), anything else = broken (stop)
  check.sh       # optional: fast assertion that the patch is present after apply
  src/           # Lean sources / templates the apply script installs or merges into the TRACKED Entrant files
  PATCH.md       # what it changes, expected ΔT/ΔQ, proof anchors, owner brief, last leader it applied to
  ENABLED        # present = included by restack; remove to park the patch
```

Rules:
- `apply.sh` must work against a **fresh** leader checkout, with no prior state. Package into files the leader already tracks: new untracked Lean files fail
  the source gate (we commit only in submission checkouts).
- Never edit protected files. Use only `BENCH`; never hard-code `~/shorecdlp`.
- When the leader absorbs or supersedes a patch, its `apply.sh` exits 3 and the restack report says so. Then update its `PATCH.md` and the `docs/LEVERS.md` row.

Run the whole stack with `formal-tools/restack.sh [leader-commit]` (defaults: `BENCH=~/shorecdlp-c`, leader = `origin/master` tip).
It resets, applies each ENABLED patch, builds, checks axioms and the boundary, scores, and writes `logs/restack-<ts>.md` with the % against the leader and the > 10 % verdict.
