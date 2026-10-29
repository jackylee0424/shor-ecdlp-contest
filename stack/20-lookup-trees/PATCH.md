# Patch 20 — width-specialized 15-bit lookup trees

Owner: Brief 15. Last validated leader: dadon bench commit `c13a293`
(`c6a88fc` leaderboard provenance), 2026-10-29.

## Change

The nine physical 15-bit left windows now use a 14-level lookup tree with
16,384 leaves. The 32,768-row coefficient interface is retained, and a proved
alias law identifies rows `a` and `a % 16384`, so decoder and circuit semantics
are unchanged. The sixteen-bit left and right windows still use the original
15-level, 32,768-leaf tree.

The patch also transports the new counts through Fourier metadata and the
rounded decoder, and supplies a specialized cancellation patch for the narrow
body. Original `Main.lean` credits are retained and the research-lab/Codex
contribution is appended.

## Resources

Compared with `c13a293`:

- Qubits: 855 → 855 (ΔQ = 0).
- Official T model: 15,365,238,944 → 15,351,820,448
  (ΔT = −13,418,496; nine times 1,490,944).
- Measurements: 921,088,792 → 919,171,864
  (Δ = −1,916,928; nine times 212,992).
- Q×T: 13,137,279,297,120 → 13,125,806,483,040
  (Δ = −11,472,814,080, or −0.08733%).
- The specialized correction has T = 1,576,701 instead of 3,067,645 and a
  proved gate-slot bound 220,684,182 instead of 1,183,793,236. Its complete
  prepared window is bounded by 2,000,000,000 slots instead of 3,000,000,000.
  The aggregate certificate retains the leader's conservative uniform slot
  envelope.

The pre-cancellation circuit bound is 15,386,520,848 T. The leader's existing
30-window rewrite still proves a 34,700,400-T reduction, yielding the official
15,351,820,448 bound.

## Proof anchors

- `Lookup15Scratch.rows_route`, `constantPoint_aliased`, and
  `left15_coefficients_aliased`: 14-bit addressing and semantic aliasing.
- `Lookup15Scratch.sources_coherent`, `actual_run`, and `actual_coherent`:
  coherent semantic equivalence of the specialized physical body.
- `Lookup15Scratch.correction_count`, `actual_count`, `correction_t`,
  `actual_t`, `correction_slots`, and `actual_slots`: exact measurement/T
  counts and proved slot bounds.
- `Single.signedWindow_count`, `signedWindow_t`, `left_metadata`, and
  `left_axis_t`: width-sensitive resource aggregation.
- `Optimization.narrowCorePatch` through `narrowActualPatch`: preservation of
  the leader's post-cancellation rewrite.

Validation from a clean `c13a293`: `build.sh`, `axioms.sh`, `boundary.sh`, and
`score.sh`; accepted with exactly `propext`, `Classical.choice`, and
`Quot.sound`.
