# Brief 22 — BUILD the exact fast multiplier as stack patch 30 on the current leader (XL, milestone by milestone)

Read `AGENTS.md`, `stack/README.md`, **`docs/FAST-MUL-FEASIBILITY.md`** (brief 20: feasible at w = 0; the quotient-flag fix is to canonicalize the signed modular
add before doubling/halving, so the quotient equals the result's low bit and one CNOT clears it; the 25-lane sites use 1 flag lane + 24 lanes of chunked carry), `docs/MUL-PLAN.md`,
`workspace/fastmul_feasibility.py`, and the checked scratch `workspace/FastMulAlgebra.lean`, `workspace/FastMulFlag.lean`, `workspace/MulClean.lean`.

## Base

Leader **spariev `c96133a` (bench `32b7d38`): 856 × 8,480,934,044 = 7,259,679,541,664.** It uses 266/208 bits with neighbour decoding (55 wrappedShift trials from one
sample), **29 corrected windows**, the temporary-AND compiler with **4-P catalyst lowering** (each eligible CCX → 4 P), all-four EEA cancellation, and a borrowed flag.
Its window arithmetic (Horner multiply/square at 4,344 CCX/bit, 8 calls per window: five sites with 68–69 clean lanes, three with 25) is as brief 20 audited. **Re-check
that on this base first.** Submissions are on hold; this is a build.

Bench: **`~/shorecdlp`** (clean at `32b7d38`). Prefix formal-tools with `BENCH=/home/gitzard/shorecdlp`. Don't touch `~/shorecdlp-c` (brief 23) or `~/shorecdlp-m`.

## Milestones (each must compile with `--wfail`; no sorry/axiom/native_decide/bv_decide; record progress in the experiment note after each)

- **M1:** re-price on this base: per-call worst-case CCX for the exact design, priced with the leader's 4-P lowering, and the projected score and % vs 7,259,679,541,664.
  Stop if < 2 %.
- **M2:** canonical signed modular add/sub cell as a `Straight` builder: correctness mod p for all inputs, clean scratch, counts, support.
- **M3:** doubling/halving with the quotient = low-bit erasure (one CNOT) proved on bench semantics. Then chunked carry passes for the 24-lane schedule.
- **M4:** the full exact multiplier/squarer (signed-digit Horner + merged pseudo-Mersenne fold): correctness, worst-case count, support within each site's clean lanes.
- **M5:** swap into the six multiply sites and two square sites through Entrant terms, and redo the window/program resource chain so the leader's lowering credit still covers
  the new cells (they must stay unconditional literal CCX).
- **M6:** package as `stack/30-fast-multiplier/` (`apply.sh` on a fresh `32b7d38`, tracked files only), then build, axioms, boundary, score, snapshot. Report the exact % vs the leader.

## Record

`work-notes/experiments/2026-10-29-fastmul-build.md` (one section per milestone, with wall times), SCOREBOARD row when scored, LOG/HANDOFF, LEVERS C8.
Don't submit or commit. Attribution: the leader's credits plus ours (exact fast multiplier; algorithm lineage ecdsa.fail modp_ft).
