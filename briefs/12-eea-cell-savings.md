# Brief 12 — cut T inside the EEA inversion wrappers, on top of the current frontier

Read `AGENTS.md`, `work-notes/HANDOFF.md`, `docs/CONTRIBUTIONS-PLAN.md` §3 (exact T breakdown), `docs/ECDSAFAIL-TRICKS.md`
("Top three" §2: source-bound EEA cell optimization), `docs/RELATED-WORK.md` §2–3 (exact AND erasure, phase-only compare, carry reuse)
and `docs/ECDLP-AI-GOLD.md` (exact Gold cells).

## Situation

- The leaderboard best (and our base) is **e-man07 `ff1bf8d`**: **855 × 86,239,836,030 = 73,735,059,805,650**. It is the upstream
  streaming construction with ArthurOstapenko's in-place XOR exceptional correction (`c4cfd7c`) and averaged 27/50 acceptance → 6 rounds (`69a9e23`).
  The bench `~/shorecdlp` is reset to it (commit `93051d2`, clean) and it reproduces locally. Snapshot: `entrants/20261029-1355-frontier-ff1bf8d`.
  Its Entrant: `Main.lean`, `Streaming/{Certificate,Correction,Resources,Semantics}.lean`. Per-round T is 14,373,306,005.
- From the upstream breakdown (§3), the **four measured EEA forward/reverse wrappers are 445,480,420 T per addition window = 86.7 % of a round**
  (28 addition windows per round, 6 rounds). The next items are Horner multiply (46.6M/window, 9.1 %) and square/subtract (15.6M, 3.0 %).
  **Every 1 % of EEA T is about 0.87 % of the score.** Any strictly lower certified score beats the leader.

## Phase 1 — exact inventory (write it down before proving anything)

Using the protected sources (`ShorECDLP/Submission/2607_13816/{EEA,Arithmetic,Challenge}` at `origin/master`, plus the Entrant's
`Streaming/*.lean`), produce `workspace/eea_inventory.py`. It must reproduce **445,480,420 T per window exactly** from per-cell counts:
the fixed 1,620-microstep schedule, the cell kinds per microstep (`MeasuredAnd`, `MeasuredSchedule`, `GidneyCarry`, comparisons, conditional
swaps/rotations, length/location controls), each cell's CCX count, and how many of them are coherent cleanups versus measured erasures.
Cite the count lemmas (`MeasuredScheduleCounts`, `MeasuredPrimitiveCounts`, `Block*PrimitiveCounts`, `IndexedStepPrimitiveCounts`, ...).
Write `docs/EEA-INVENTORY.md`: the top 10 cells by total T, and for each candidate **exact** rewrite the T saved per window and per round,
and the proof effort. Candidates to check:
- coherent uncomputations that could be measurement-based (0 T + Clifford fix; the bench has `measuredAndErase_coherent_uncompute`);
- phase-only comparisons (compute only the phase a comparison controls; Gold `compare_phase_exact`);
- repeated identical AND products that can be computed once and held (`ctx_holds` idea);
- controlled operations whose control is a known constant per microstep (`whenBit`/schedule specialization; `run_fold` idea);
- carry chains that use full adders where a Gidney logical-AND adder suffices;
- Horner multiply / square if a cheaper exact cell applies there too.

Only exact rewrites. No approximate or statistical windows.

## Phase 2 — implement the best one or two

Implement the highest saving-per-effort rewrite as Entrant-side definitions that wrap or replace the protected builders. Protected files can't change:
define new terms in the Entrant and re-prove what the certificate needs (run/coherence correspondence, counts, support ≤ 855, records/stride, `UniformT`, gate slots),
keeping the acceptance chain unchanged. Records may change, so recompute the stride and the decoder positions.
Package into the **existing tracked Entrant files** (you can't commit; new untracked Lean files fail the source gate), then `formal-tools/build.sh`,
`axioms.sh`, `boundary.sh`, `score.sh`, `snapshot.sh eea-<slug> "<score>"`. The score must be **strictly below 73,735,059,805,650**.
Ship the first strict improvement as soon as it is accepted, then continue with the next rewrite.

## Constraints

Only `~/shorecdlp/ShorECDLP/Submission/Entrant/` may change in the bench. No sorry/axiom/native_decide/bv_decide. Linter-clean (`--wfail`).
Do not submit, push, or commit.

## Record

`work-notes/experiments/2026-10-29-eea.md`, SCOREBOARD rows for scored candidates, LOG and HANDOFF. Attribution in `Main.lean`: keep the existing upstream
and ArthurOstapenko/e-man07 credits, and add a line for our EEA change.
