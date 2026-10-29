# Brief 15 — stack patches: width-specialized 15-bit lookup trees (≈ −0.16 %) + one fewer right window (≈ −3.3 %, if provable)

Read `AGENTS.md`, **`stack/README.md`** (the patch contract), `docs/LEVERS.md` (rows E2, E3) and **`docs/FEWER-WINDOWS.md`** ranks 1–3 with
`workspace/fewer_windows.py`.

## Base and bench

The leader is dadon `c6a88fc` (bench commit `c13a293`; 263-bit left, 224-bit physical right rounded to a 203-bit wrappedShift word, 1 direct load + 30 corrected windows): 855 qubits, Q×T 13,137,279,297,120 (855 × 15,365,238,944); submission bar for the whole stack: < 11,823,551,367,408. Your bench is **`~/shorecdlp`** (clean at `c13a293`).
Prefix formal-tools with `BENCH=/home/gitzard/shorecdlp` (that's the default). Don't touch `~/shorecdlp-m` (brief 16) or `~/shorecdlp-c` (restack).

## Deliverable: two patches in the stack format

1. `stack/20-lookup-trees/`: width-specialized physical lookup trees for the 15-bit signed windows (16,384 leaves instead of aliasing 32,768). Semantics
   are unchanged; the T and gate-slot reduction is proved. Expected from FEWER-WINDOWS rank 2: about −0.16 %.
2. `stack/21-right208/`: **drop one right window.** The leader measures the right axis at 224 physical bits (14 × 16) but decodes only a rounded 203-bit word,
   using a circular concentration bound (radius 512 → mass ≥ 999/1000) and `coarseRound b = ((b + 2^20)/2^21) % 2^203`. Measuring **208 bits (13 windows)** leaves 5 slack bits
   (radius ≈ 16). Price exactly first: the combined success (left 263-bit nearest-numerator mass × right rounding-window mass, as the leader's proof composes them) must be
   ≥ 0.99 uniformly; a naive Fejér tail gives ≈ 0.987 at radius 16, so a sharper bound is needed (exact finite kernel, or the leader's inverse-square tail done tighter),
   or a re-split (for example 209–212 physical bits with one narrower window, if the row cap and the decoder's 203-bit word allow). Also check whether trimming the left axis (263 → 262)
   frees enough margin. Implement only if the exact numbers clear 0.99; otherwise write the no-go with numbers in `PATCH.md` and park the patch.

For each: `apply.sh` (idempotent, operates on `$BENCH`, edits only the leader's **tracked** Entrant files, exits 3 if the leader has already absorbed it),
`src/`, `PATCH.md` (ΔT, ΔQ, proof anchors), and `ENABLED` once it builds and scores. Validate by resetting the bench to `c13a293` and running your
`apply.sh` from scratch, then `formal-tools/build.sh`, `axioms.sh`, `boundary.sh`, `score.sh`. Do patch 20 first and ship it, then 21.

## Constraints and record

No sorry/axiom/native_decide/bv_decide. Linter-clean (`--wfail`). Don't submit or commit. Experiment note `work-notes/experiments/2026-10-29-precision262.md`,
SCOREBOARD rows (scored in your bench), LOG/HANDOFF, LEVERS rows E2/E3. Attribution: keep the leader's `Main.lean` credits and add ours.
