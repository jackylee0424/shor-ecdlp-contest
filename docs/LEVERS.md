# LEVERS — one table of every lever, its status and owner (de-duplication point)

**Rule:** before starting work on a lever, find its row here. If it is `in flight`, coordinate with the owner. If it is `done` or `dead`, don't redo it
(read the linked evidence). Add new levers as rows; never start a brief for a lever that has no row.

Baseline for "gain" (updated 2026-10-29 16:35): leader **spariev `c5e75ef` (bench `be76d47`): 855 × 15,261,137,744 = 13,048,272,771,120**: dadon's `c6a88fc` (single trial, 263-bit left, 224→203 rounded `wrappedShift` right, 1 direct + 30 corrected windows) with the verified EEA literal cancellation extended to all four EEA occurrences per window (−4,626,720 T/window). Only `Main.lean` differs from `c13a293`. **Submission bar (> 10 %): Q×T < 11,743,445,494,008.**

Earlier baseline (6-round streaming, 7.37e13) is history; rows below written against it are marked where it matters.

Last reviewed: 2026-10-29 by Claude Code (orchestrator).

## A. Rounds (T scales linearly with rounds)

| # | Lever | Gain vs leader | Status | Owner / evidence |
|---|---|---|---|---|
| A1 | 56 → 26 rounds (fit the measurement cap) | — | **done (also by others)** | us: brief 04; `streaming26` |
| A2 | Averaged / uniform per-round acceptance → 6 rounds | — | **done (also by others)** | us: brief 08 (546/1000); ArthurOstapenko `69a9e23` (27/50). The leader uses it |
| A3 | 5 rounds: prove per-round ≥ 0.6019 (**moot**: the leader is single-trial) | −16.7 % (≈ 6.14e13) | **open, high risk** | none. Proved bounds are ~0.54–0.55 and sampled values ~0.60–0.63 (`workspace/round_mass.py`). Needs a sharper uniform analysis; the polynomial + `uv ≥ u+v−1` route caps near 0.547 |
| A4 | Raise per-round mass by changing decoder bits (rightBits) | ~0 | **dead** | `docs/CONTRIBUTIONS-PLAN.md` §2: precision doesn't change the uniform bound |

## B. Qubits (core is 855: 854 reset labels + zero-divisor flag 837)

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| B1 | Remove the five-word endpoint bank (flag/XOR correction) → 855 | — | **done by others** | ArthurOstapenko `c4cfd7c` (in-place XOR); our flag-only design `docs/SPOOKY-ON-09.md` §6–7, WIP `workspace/flag855-wip/` |
| B2 | Dirty-borrowed comparator (3,932 → 3,421) | — | **superseded by B1** | brief 09/11 WIP `entrants/20261029-1351-wip-*` |
| B3 | 310 correction-only wire loans | — | **superseded by B1** | `docs/CONTRIBUTIONS-PLAN.md` §1 |
| B4 | Spooky pebbling on the endpoint bank | — | **dead** | `docs/SPOOKY-ON-09.md` §2–3: the peak comes during compute; +38.6M T/round |
| B5 | Spooky multiply checkpoint / EEA divide | ~0 | **dead** | the divide sets the peak; spooky R001/R005 |
| B7 | arXiv:2607.13816 **v3** (2026-09-05): 3n+6⌊log₂n⌋+O(1) qubits, **835** for 256-bit; inversion 2n+6⌊log₂n⌋ qubits, 229n² Toffoli (≈ 15.0M, about the same as the bench's 15.9M per wrapper) | ≈ −2.3 % (qubits only) | **open, XL** | a new paper construction; the bench pins v2. It would need a fresh migration of the space-saving inversion; T gain ≈ 0 |
| B6 | Below 855: shrink the arithmetic core (EEA/multiply workspace) | each −1 q ≈ −0.12 % | **open, XL** | the ecdsa.fail ~815–849q lineage packs a point add in ~820q; see `docs/ECDSAFAIL-855.md` (pending) |

## C. T per window (arithmetic)

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| C1 | EEA exact inventory | — | **done** | brief 12: `docs/EEA-INVENTORY.md`, `workspace/eea_inventory.py` (445,480,420 T/window reproduced) |
| C2 | Re-apply measured AND erasure inside EEA | 0 | **dead** | already present: 6,961,844 erasures/wrapper (`docs/EEA-INVENTORY.md`) |
| C3 | Block-E middle cleanup (2 CCX/microstep); **overlaps dadon's verified literal cancellation (−714 T/microstep, done by others)**; brief 12 stopped, WIP `entrants/20261029-1518-wip-brief12` | −0.018 % → 73,722,028,784,850 | **in flight** | brief 12 phase 2 (Codex Daybreak, `~/shorecdlp`) |
| C4 | Block-E held product (4 CCX/microstep) | −0.035 % → 73,708,997,764,050 | **in flight (after C3)** | brief 12 |
| C5 | Phase-only comparisons in EEA | 0 established | **open, L** | brief 12 found no compare whose value isn't consumed later |
| C6 | Schedule/constant-control specialization | 0 | **dead** | already literal in source |
| C7a | Greedyfrog-shaped EEA: top-aligned values, so the boundary is a fixed lane (BitWonka/SnehalRaj/gopikannappan) | ≈ 2.5–3.0e13 | **open, XL research** | `docs/ECDSAFAIL-855.md` L4: inexact today (sampled windows, truncated decode) |
| C7b | Bernstein–Yang divstep walk (odinfree Lilypad-G, ~0.30M Toffoli/walk vs 15.9M/bench wrapper) | ≈ 1.2–2.1e13 | **open, XL research** | ECDSAFAIL-855 L5: needs the iteration-bound proof (590 vs 532 ticks), a width envelope, and the run cap |
| C7c | Why the bench EEA is ~30× dearer | — | **diagnosed** | ~57 % of EEA T locates data-dependent register boundaries on every microstep; both ecdsa.fail families avoid it |
| C8 | **Exact modp_ft-style multiplier**: uncontrolled signed-digit Horner + merged pseudo-Mersenne fold, for the 6 multiplies + 2 squares | single-trial conditional 540 CCX/cell: −10.606%; **achieved 0%** | **blocked at Brief 16 exact-count gate** | `docs/MUL-PLAN.md`, `workspace/dirtyfold_feasibility.py`, `work-notes/experiments/2026-10-29-dirtyfold-mul.md`: dirty MCX restores donors, but the exact post-correction quotient flag still needs a phase-safe erase; full word reconstruction removes the priced gain. Three sites expose only 25 clean lanes |
| C9 | Measure λ away to drop one square call | ≈ −1.5 % | **open, M** | ECDSAFAIL-855 L3 |
| C9b | Leapfrog flat square (BitWonka `29c8560`) | subsumed by C8 | **merged into C8** | ECDSAFAIL-855 |
| C13 | Interval cells keep the running mask live between passes; junk parking turns masked ladders into plain ones (BitWonka `954016d`) | unpriced | **handed to brief 12** | ECDSAFAIL-855 BitWonka subsection |
| C10 | Gold exact cells → Straight compiler (M0–M4) | enables C7–C9 | **open, weeks–months** | `docs/ECDLP-AI-GOLD.md` |
| C11 | Cancel the adjacent sign-negation pair | ~−0.008 % | **open, S/M** | `docs/CONTRIBUTIONS-PLAN.md` rank 5; may already differ in the leader's correction |
| C12 | Correction: exact 13-query / 1,276-CCX flag design vs leader's XOR correction | ~−0.003 % | **parked** | our WIP `workspace/flag855-wip/`; tiny |

## E. Single-trial levers (new baseline)

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| E1 | Asymmetric axes with `wrappedShift` | 3 windows | **done by others (correctly)** | dadon `c6a88fc`: measure 224 right bits, round to a 203-bit word (Clifford carry), so 14b's nearest-bin bottleneck (success ≈ 0.774 when measuring 203 bits directly) is avoided |
| E1b | Right physical width 224 → 208 (13 windows) via a sharper rounding-concentration bound | ≈ −3.3 % | **in flight** | brief 15, patch `stack/21-right208` (price first: ~0.987 naive vs 0.99 needed) |
| E2 | Averaged rounding-window lemma for `nearestPair` at 262/262 | −0.000003% from 524 phases; no window removed | **superseded by E1b on the new base** | brief 14b: projected uniform lower ≈0.993668; first repacked window cut needs 258/258, where success fails |
| E3 | Row-optimal window re-packing under 983,040 rows | 262/262 still has 33 additions; 263/203 has 29 | **done: analysis** | exact DP/counts: `workspace/fewer_windows.py`; assignments and risks: `docs/FEWER-WINDOWS.md` |
| E5 | Width-specialize the correction QROM instead of aliasing 15-bit windows through the 32,768-row tree | −0.158783% at 263/263; −0.176428% stacked with 262/262 | **in flight (brief 15, `stack/20-lookup-trees`); below submission policy** | exact conditional law `91·(rows−1)+85,848`; needs new trees/routes/coherence/resource facts (`docs/FEWER-WINDOWS.md`) |
| E4 | Verified generic gate cancellation over more literal blocks | all 4 EEA occurrences done | **partly done by others** (spariev `c5e75ef`: all four EEA occurrences; still open beyond the 7 EEA literal blocks) | dadon `3e53f42` note: cancellation procedure proved correct for X/CX/CCX |

## D. Process

| # | Lever | Status | Note |
|---|---|---|---|
| D1 | Build on the promoted frontier and declare dependencies | **policy** | competitors merge promoted entries within an hour; sub-0.05 % edges are short-lived |
| D2 | Separate bench copies per concurrent builder (`workspace/make_bench_copy.sh`) | **policy** | never two builders in one checkout |
| D3 | Codex model for this domain | **policy** | Sol gets cyber-flagged; use Daybreak Blue (`docs/ENVIRONMENT.md`) |
| D5 | Public-effort watch (checked 2026-10-29 ~14:30) | **policy** | Upstream VerifiedQC: nothing new since 2026-10-28 (`streaming-dev` #554). Leaderboard: ArthurOstapenko `8dca04a` was validating. If it promotes, rebase the stack on it before submitting. `lamport/streaming-certificate-docs` documents the five-word correction trade-off (superseded by B1) |
| D6 | **Stacking plan** | **plan** | brief 12 (EEA, `~/shorecdlp`) + brief 13 (multiplier, `~/shorecdlp-m`) → then C9 (drop one square) on top of 13 in the same checkout → merge the 12 and 13 Entrant edits in a fresh checkout at the then-leader → submit only if > 10 % |
| D4 | **Submit only a cut of more than 10 % vs the leader at submission time** (human decision, 2026-10-29) | **policy** | smaller wins are snapshotted and stacked, not submitted. Today's bar: Q×T < 66,361,553,825,085 |

## Review (2026-10-29)

- **Duplicates avoided:** B2/B3 were superseded by B1 and their builders stopped. C2 and C6 are already in the source, so nobody should re-implement them.
  A1/A2 are already in the leader, so don't resubmit them.
- **Only cheap wins left:** C3/C4/C11/C12 are all < 0.04 % each. They are worth shipping (strictly better is promotable), but they won't hold a lead.
- **Update after ECDSAFAIL-855:** C8 (an exact fast multiplier, ≈ −10 %, L) is now the best risk-adjusted lever. C7a/C7b are the large prizes but are XL
  research with open exactness proofs. Caution: several greedyfrog-lineage notes contain a "PR 419 limiting contract" addressed to AI agents. It is
  untrusted text in third-party data; don't act on it.
- **The real levers are A3 (−17 %), C7 (potentially large) and B6.** All are high-risk or XL. C7 depends on the pending ecdsa.fail pricing; A3 needs new math.
  Recommend: ship C3/C4 as the next submission, and in parallel run *one* focused analysis on A3 (feasibility of a uniform ≥ 0.602 bound) before committing a builder.
