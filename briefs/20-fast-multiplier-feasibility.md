# Brief 20 — fast multiplier feasibility research (C8), with extra wires allowed

Read `AGENTS.md`, `docs/LEVERS.md` (C8, G-rows), **`docs/MUL-PLAN.md`** (briefs 13 and 16: the 25-lane sites, why the dirty fold stopped),
**`docs/QUBITS-FOR-GATES.md`** (brief 18: the C8 exception at ~540 CCX/bit with a ~45-wire pool → 901 qubits), `docs/ECDSAFAIL-855.md` (L1/L2),
`workspace/FastMulAlgebra.lean`, `workspace/MulClean.lean`, `workspace/dirtyfold_feasibility.py`.

## Context

Target program: patch 10, the temporary-AND compiler on spariev's 30-window entrant (base `a72f4af`): **856 × 11,513,899,424 = 9,855,897,906,944**. Every
unconditional CCX now costs **5** (not 7). The window's multiply/square calls use the protected Horner multiplier, **4,344 CCX/bit**; there are 8 calls per window
(5 sites with 68–69 clean lanes, 3 with 25). Brief 16's exact-count gate failed because **no proved phase-safe method erases the post-correction quotient flag**
inside the fast cell, and the donor design (≈ 540 CCX/bit) relies on three **approximate exceptional-state** steps.
Score rule: adding k wires pays only if ΔT/T > k/856 (≈ 13.45M T per wire).

## Research questions (feasibility only; no Entrant integration)

1. **The quotient-flag erasure.** Design an exact way to erase the pseudo-Mersenne fold's quotient/overflow flag after correction: recompute-and-measure,
   a phase-only comparison (compute only the phase the flag controls), a Gidney-style measured AND with a Clifford fix-up, or holding the flag in an extra wire until a
   later point where it can be measured. Prove the key identity in Lean scratch (`workspace/FastMul*.lean`, check with `BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh`)
   on the bench semantics (`MeasurementUncompute`, `MeasuredAnd`), or state precisely why it fails.
2. **The three approximate exceptional states.** For each, give an exact replacement and its worst-case CCX cost (for example a full-width carry instead of a truncated one, or an
   extra correction pass) and how many wires it needs.
3. **Exact worst-case count per call**, at the 68–69-lane sites and at the 25-lane sites, with and without a shared extra-wire pool of size w (w = 0 … 64). Price everything with the
   compiler (CCX → 5; measured erasures → 0) and give the total ΔT, the qubits, the score, and the % against patch 10 and against the leader 9,857,180,674,304.
4. **Verdict:** feasible / infeasible / feasible-with-k-wires; the best (w, design) point; and the Lean effort (S/M/L/XL) to build it as a stack patch on `a72f4af` + patch 10.

## Constraints and output

Read-only on all bench checkouts. Lean scratch only via `BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh` (never build in `~/shorecdlp` = brief 19 or `~/shorecdlp-m` = brief 17).
No submissions or commits. Write `docs/FAST-MUL-FEASIBILITY.md` (verdict first), `workspace/fastmul_feasibility.py` (exact integers), Lean scratch, a LOG line, and update LEVERS C8.
