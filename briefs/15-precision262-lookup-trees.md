# Brief 15 — stack patch: 262/262 precision + width-specialized 15-bit lookup trees (≈ −0.18 %)

Read `AGENTS.md`, **`stack/README.md`** (the patch contract), `docs/LEVERS.md` (rows E2, E3) and **`docs/FEWER-WINDOWS.md`** ranks 1–3 with
`workspace/fewer_windows.py`.

## Base and bench

The leader is ArthurOstapenko `60e5072` (bench commit `b46591c`): 855 qubits, Q×T 14,351,855,116,590. Your bench is **`~/shorecdlp`** (clean at `b46591c`).
Prefix formal-tools with `BENCH=/home/gitzard/shorecdlp` (that's the default). Don't touch `~/shorecdlp-m` (brief 16) or `~/shorecdlp-c` (restack).

## Deliverable: two patches in the stack format

1. `stack/20-lookup-trees/`: width-specialized physical lookup trees for the 15-bit signed windows (16,384 leaves instead of aliasing 32,768). Semantics
   are unchanged; the T and gate-slot reduction is proved. Expected from FEWER-WINDOWS rank 2: about −0.16 %.
2. `stack/21-precision262/`: `nearestPair` at 262/262 bits (one fewer bit per axis, re-packing a 16-bit window as 15). It needs a uniform success proof ≥ 0.99
   at t = 262 (an averaged rounding-window bound; FEWER-WINDOWS gives ≈ 0.99367 as the target margin), plus the row/table and Fourier-phase recount.

For each: `apply.sh` (idempotent, operates on `$BENCH`, edits only the leader's **tracked** Entrant files, exits 3 if the leader has already absorbed it),
`src/`, `PATCH.md` (ΔT, ΔQ, proof anchors), and `ENABLED` once it builds and scores. Validate by resetting the bench to `b46591c` and running your
`apply.sh` from scratch, then `formal-tools/build.sh`, `axioms.sh`, `boundary.sh`, `score.sh`. Do patch 20 first and ship it, then 21.

## Constraints and record

No sorry/axiom/native_decide/bv_decide. Linter-clean (`--wfail`). Don't submit or commit. Experiment note `work-notes/experiments/2026-10-29-precision262.md`,
SCOREBOARD rows (scored in your bench), LOG/HANDOFF, LEVERS rows E2/E3. Attribution: keep the leader's `Main.lean` credits and add ours.
