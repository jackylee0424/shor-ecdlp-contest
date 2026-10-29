# LEVERS — one table of every lever, its status and owner (de-duplication point)

**Rule:** before starting work on a lever, find its row here. If it is `in flight`, coordinate with the owner. If it is `done` or `dead`, don't redo it
(read the linked evidence). Add new levers as rows; never start a brief for a lever that has no row.

Baseline for "gain": the current leader **e-man07 `ff1bf8d`: 855 × 86,239,836,030 = 73,735,059,805,650** (6 rounds, 28 addition windows/round,
14,373,306,005 T/round). Reproduced locally: `entrants/20261029-1355-frontier-ff1bf8d`.
Composition of T/round: EEA wrappers 12,473,451,760 (86.8 %), Horner multiply 1,305,986,808 (9.1 %), square/subtract 435,880,284 (3.0 %),
QROM/lookup ~64M (0.45 %), correction (~3.07M/window, ~0.6 %), Fourier 54,168.

Last reviewed: 2026-10-29 by Claude Code (orchestrator).

## A. Rounds (T scales linearly with rounds)

| # | Lever | Gain vs leader | Status | Owner / evidence |
|---|---|---|---|---|
| A1 | 56 → 26 rounds (fit the measurement cap) | — | **done (also by others)** | us: brief 04; `streaming26` |
| A2 | Averaged / uniform per-round acceptance → 6 rounds | — | **done (also by others)** | us: brief 08 (546/1000); ArthurOstapenko `69a9e23` (27/50). The leader uses it |
| A3 | 5 rounds: prove per-round ≥ 0.6019 | −16.7 % (≈ 6.14e13) | **open, high risk** | none. Proved bounds are ~0.54–0.55 and sampled values ~0.60–0.63 (`workspace/round_mass.py`). Needs a sharper uniform analysis; the polynomial + `uv ≥ u+v−1` route caps near 0.547 |
| A4 | Raise per-round mass by changing decoder bits (rightBits) | ~0 | **dead** | `docs/CONTRIBUTIONS-PLAN.md` §2: precision doesn't change the uniform bound |

## B. Qubits (core is 855: 854 reset labels + zero-divisor flag 837)

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| B1 | Remove the five-word endpoint bank (flag/XOR correction) → 855 | — | **done by others** | ArthurOstapenko `c4cfd7c` (in-place XOR); our flag-only design `docs/SPOOKY-ON-09.md` §6–7, WIP `workspace/flag855-wip/` |
| B2 | Dirty-borrowed comparator (3,932 → 3,421) | — | **superseded by B1** | brief 09/11 WIP `entrants/20261029-1351-wip-*` |
| B3 | 310 correction-only wire loans | — | **superseded by B1** | `docs/CONTRIBUTIONS-PLAN.md` §1 |
| B4 | Spooky pebbling on the endpoint bank | — | **dead** | `docs/SPOOKY-ON-09.md` §2–3: the peak comes during compute; +38.6M T/round |
| B5 | Spooky multiply checkpoint / EEA divide | ~0 | **dead** | the divide sets the peak; spooky R001/R005 |
| B6 | Below 855: shrink the arithmetic core (EEA/multiply workspace) | each −1 q ≈ −0.12 % | **open, XL** | the ecdsa.fail ~815–849q lineage packs a point add in ~820q; see `docs/ECDSAFAIL-855.md` (pending) |

## C. T per window (arithmetic)

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| C1 | EEA exact inventory | — | **done** | brief 12: `docs/EEA-INVENTORY.md`, `workspace/eea_inventory.py` (445,480,420 T/window reproduced) |
| C2 | Re-apply measured AND erasure inside EEA | 0 | **dead** | already present: 6,961,844 erasures/wrapper (`docs/EEA-INVENTORY.md`) |
| C3 | Block-E middle cleanup (2 CCX/microstep) | −0.018 % → 73,722,028,784,850 | **in flight** | brief 12 phase 2 (Codex Daybreak, `~/shorecdlp`) |
| C4 | Block-E held product (4 CCX/microstep) | −0.035 % → 73,708,997,764,050 | **in flight (after C3)** | brief 12 |
| C5 | Phase-only comparisons in EEA | 0 established | **open, L** | brief 12 found no compare whose value isn't consumed later |
| C6 | Schedule/constant-control specialization | 0 | **dead** | already literal in source |
| C7 | Algorithmic EEA replacement (ecdsa.fail divsteps/greedyfrog-style division at ~1.3–2.5M Toffoli per point add) | potentially large (EEA is 86.8 % of T) | **open, XL; being priced** | sub-agent → `docs/ECDSAFAIL-855.md`; exactness and worst-case of those routes are the blockers (`docs/ECDSAFAIL-TRICKS.md`, `docs/ECDLP-AI-GOLD.md`) |
| C8 | Horner multiply: exact pseudo-Mersenne fold / cheaper cells (9.1 %) | up to a few % | **open, L–XL; being priced** | sub-agent (ECDSAFAIL-855); brief 12 found no source-compatible cell yet |
| C9 | Square: Leapfrog flat square (BitWonka `29c8560`, odinfree 852) (3.0 %) | ≤ ~1 % | **open; being priced** | sub-agent (ECDSAFAIL-855) |
| C10 | Gold exact cells → Straight compiler (M0–M4) | enables C7–C9 | **open, weeks–months** | `docs/ECDLP-AI-GOLD.md` |
| C11 | Cancel the adjacent sign-negation pair | ~−0.008 % | **open, S/M** | `docs/CONTRIBUTIONS-PLAN.md` rank 5; may already differ in the leader's correction |
| C12 | Correction: exact 13-query / 1,276-CCX flag design vs leader's XOR correction | ~−0.003 % | **parked** | our WIP `workspace/flag855-wip/`; tiny |

## D. Process

| # | Lever | Status | Note |
|---|---|---|---|
| D1 | Build on the promoted frontier and declare dependencies | **policy** | competitors merge promoted entries within an hour; sub-0.05 % edges are short-lived |
| D2 | Separate bench copies per concurrent builder (`workspace/make_bench_copy.sh`) | **policy** | never two builders in one checkout |
| D3 | Codex model for this domain | **policy** | Sol gets cyber-flagged; use Daybreak Blue (`docs/ENVIRONMENT.md`) |

## Review (2026-10-29)

- **Duplicates avoided:** B2/B3 were superseded by B1 and their builders stopped. C2 and C6 are already in the source, so nobody should re-implement them.
  A1/A2 are already in the leader, so don't resubmit them.
- **Only cheap wins left:** C3/C4/C11/C12 are all < 0.04 % each. They are worth shipping (strictly better is promotable), but they won't hold a lead.
- **The real levers are A3 (−17 %), C7 (potentially large) and B6.** All are high-risk or XL. C7 depends on the pending ecdsa.fail pricing; A3 needs new math.
  Recommend: ship C3/C4 as the next submission, and in parallel run *one* focused analysis on A3 (feasibility of a uniform ≥ 0.602 bound) before committing a builder.
