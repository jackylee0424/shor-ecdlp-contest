# LEVERS — one table of every lever, its status and owner (de-duplication point)

**Rule:** before starting work on a lever, find its row here. If it is `in flight`, coordinate with the owner. If it is `done` or `dead`, don't redo it
(read the linked evidence). Add new levers as rows; never start a brief for a lever that has no row.

Baseline for "gain" (updated 2026-10-29 ~17:45): leader **spariev `c96133a` (bench `32b7d38`): 856 × 8,480,934,044 = 7,259,679,541,664**: 266/208 bits with neighbour decoding (55 `wrappedShift` trials from one sample, radius 27), **29 corrected windows**, temp-AND compiler with **4-P catalyst lowering**, all-four EEA cancellation, borrowed flag. (i34-9 `03bad79` widened the lowering credit to every window Toffoli.) **Submissions on hold.** In flight: brief 22 (build the exact fast multiplier, `~/shorecdlp`). Brief 23 is complete (B7/C7a--d).

Earlier baseline (6-round streaming, 7.37e13) is history; rows below written against it are marked where it matters.

Last reviewed: 2026-10-29 by Claude Code (orchestrator).

## A. Rounds (T scales linearly with rounds)

| # | Lever | Gain vs leader | Status | Owner / evidence |
|---|---|---|---|---|
| A1 | 56 → 26 rounds (fit the measurement cap) | — | **done (also by others)** | us: brief 04; `streaming26` |
| A2 | Averaged / uniform per-round acceptance → 6 rounds | — | **done (also by others)** | us: brief 08 (546/1000); ArthurOstapenko `69a9e23` (27/50). The leader uses it |
| A3 | 5 rounds: prove per-round ≥ 0.6019 (**moot**: the leader is single-trial) | −16.7 % (≈ 6.14e13) | **open, high risk** | none. Proved bounds are ~0.54–0.55 and sampled values ~0.60–0.63 (`workspace/round_mass.py`). Needs a sharper uniform analysis; the polynomial + `uv ≥ u+v−1` route caps near 0.547 |
| A4 | Raise per-round mass by changing decoder bits (rightBits) | ~0 | **dead** | `docs/CONTRIBUTIONS-PLAN.md` §2: precision doesn't change the uniform bound |

## B. Qubits (855 total: 854 reset labels + compiler ancilla 1024; old flag 837 is absent)

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| B1 | Remove the five-word endpoint bank (flag/XOR correction) → 855 | — | **done by others** | ArthurOstapenko `c4cfd7c` (in-place XOR); our flag-only design `docs/SPOOKY-ON-09.md` §6–7, WIP `workspace/flag855-wip/` |
| B2 | Dirty-borrowed comparator (3,932 → 3,421) | — | **superseded by B1** | brief 09/11 WIP `entrants/20261029-1351-wip-*` |
| B3 | 310 correction-only wire loans | — | **superseded by B1** | `docs/CONTRIBUTIONS-PLAN.md` §1 |
| B4 | Spooky pebbling on the endpoint bank | — | **dead** | `docs/SPOOKY-ON-09.md` §2–3: the peak comes during compute; +38.6M T/round |
| B5 | Spooky multiply checkpoint / EEA divide | ~0 | **dead** | the divide sets the peak; spooky R001/R005 |
| B7 | arXiv:2607.13816 **v3**: 579-wire standalone inversion / 835-wire standalone point add, 229n² leading Toffoli term | 0 established | **not a separate candidate; same bench architecture** | Brief 23: the protected 1,620-step packed/location-controlled EEA and Figure 15 shell are v3's construction. The challenge peak also has the coherent address bank and two compiler wires. V3's 15.35M is rounded Qiskit/template output; kernel counts are 15,910,015 raw and 15,744,775 CCX after leader cancellation. `docs/SMALLER-EEA.md` |
| B6 | Below 855: shrink the arithmetic core (EEA/multiply workspace) | each −1 q ≈ −0.12 % | **censused; open, XL** | Brief 21: every physical owner is live at the EEA peak; the ecdsa.fail 815–849q layouts are different/partly approximate algorithms, not local loans. Exact curve and technique map: `docs/FEWER-QUBITS.md` |
| B8 | Remove the temporary-AND compiler ancilla | −1 q, but +3,745,739,760 T; score **+32.380951297%** | **dead on score; exact** | Brief 21: the 854-wire Parent is 854×15,258,353,144=13,030,633,584,976. A competitive 854 build has only +13,480,811 T of room |
| B9 | Dynamic compiler-ancilla loan from an arithmetic owner | target −1 q; must add ≤13,480,811 T total | **blocked by census; XL** | no clean owner exists at lowered EEA CCX sites; 2,696,162 compiled CCX is the exact 5T acceptance cap. `workspace/fewer_qubits.py` |
| B10 | Fold/recompute the address/Fourier bank or loan the repair suffix 578..579 | 0 established | **unpriced research** | bank is coherent through the binding EEA; suffix has no disjoint unique owner to replace. Per-phase lifetimes: `docs/FEWER-QUBITS.md` |

## C. T per window (arithmetic)

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| C1 | EEA exact inventory | — | **done** | brief 12: `docs/EEA-INVENTORY.md`, `workspace/eea_inventory.py` (445,480,420 T/window reproduced) |
| C2 | Re-apply measured AND erasure inside EEA | 0 | **dead** | already present: 6,961,844 erasures/wrapper (`docs/EEA-INVENTORY.md`) |
| C3 | Block-E middle cleanup (2 CCX/microstep); **overlaps dadon's verified literal cancellation (−714 T/microstep, done by others)**; brief 12 stopped, WIP `entrants/20261029-1518-wip-brief12` | −0.018 % → 73,722,028,784,850 | **in flight** | brief 12 phase 2 (Codex Daybreak, `~/shorecdlp`) |
| C4 | Block-E held product (4 CCX/microstep) | −0.035 % → 73,708,997,764,050 | **in flight (after C3)** | brief 12 |
| C5 | Phase-only comparisons in EEA | 0 established | **open, L** | brief 12 found no compare whose value isn't consumed later |
| C6 | Schedule/constant-control specialization | 0 | **dead** | already literal in source |
| C7a | Exact greedyfrog-shaped EEA: top-aligned values, fixed boundary, full inverse decode | conditional screen **841×3,161,104,444 = 2,658,488,837,404** (−63.380080%), not a bound | **open, XL; decode blocker** | Brief 23: 469-slot screen uses the 405 quotient-weight theorem plus an unproved ≤2n renormalisation theorem. Donor windows and 28-lane/21-row decode remain sampled; no exact Q/count exists. `docs/SMALLER-EEA.md` |
| C7b | Exact Bernstein–Yang divstep walk with proved horizon, fixed width and replay | modular cofactors close the growing-width/scaled-decoder blocker; local tag-free replay is refuted; proved tagged screen loses | **Brief 27 stop; reopen only with packed physical cell + reachable-state decoder** | `workspace/DivstepTight.lean` proves canonical `n`-bit modular cofactors `(B,D)`, direct terminal inverse, two-bit tagged replay, n=8/n=12 all-input envelopes, and a three-way even/swap/add collision ruling out any post-state-only local inverse. At n=256 the exact arithmetic state is 1,048 lanes (`257+257+256+256+12+10`). The optimistic N=590 two-bit-tag screen is **3,018×3,582,256,364=10,811,249,706,552** (+48.921859%); parity/checkpoint storage still screens +27.555668%. Even impossible zero history is only −9.304713% before the missing modular-half surcharge. The old W=340/703-CCX cell, termination theorem, physical `Straight`, and packed invariant remain unproved. `docs/DIVSTEP-TIGHT.md` |
| C7c | Why the bench EEA is ~30× dearer | — | **exactly diagnosed** | B/E repeated boundary location is 9,059,900 raw CCX/wrapper, 8,943,260 after assigning the leader cancellation: 56.80% of the effective 15,744,775 CCX. `docs/SMALLER-EEA.md` |
| C7d | Keep the bench recurrence but cache/normalise boundaries | exact zero-cost floor **856×4,331,261,404 = 3,707,559,761,824** (−48.929429%); no circuit attains it | **open, L/XL; floor only** | Same packed state cannot make boundaries fixed for free. Cached one-hot masks push Q toward ≥1,112; normalisation changes the recurrence. Need actual mask/layout/count theorem before a patch. `docs/SMALLER-EEA.md` |
| C8 | **Exact fast multiplier**: canonical signed add followed by exact double/halve; full-width chunked pseudo-Mersenne passes at the 6 multiplies + 2 squares | corrected direct phase-safe fallback: **856×8,419,666,672 = 7,207,234,671,232** (−0.722413% vs leader `32b7d38`); achieved Entrant cut 0% | **Brief 22 stopped at corrected M1 (<2%)** | Brief 20's one-pass price omitted quantum-sign selection between the add/sub quotient predicates. `workspace/FastMulCarry.lean` checks the 503-CCX tight chunk pass and quadratic mask-carry MBU, but the exact phase-safe sign selection needs add/compare/unadd plus overflow cleanup. `work-notes/experiments/2026-10-29-fastmul-build.md`, `workspace/fastmul_build.py` |
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
| E1b | Right physical width 224 → 208 (13 windows) via a sharper rounding-concentration bound | conditional −3.34% | **parked: 208–210 fail success; 211 is numerically plausible but unproved** | brief 15, `stack/21-right208/PATCH.md`: combined limiting masses 0.96690, 0.97987, 0.98690, 0.99069 for 208–211 bits; 211 also needs three width-17 trees and a 17th bank wire |
| E2 | Averaged rounding-window lemma for a 262-bit left axis | enables row-tight left262/right212 re-split | **open proof dependency** | brief 15: left262/right212 fits exactly 983,040 rows and has limiting union diagnostic ≈0.994519, but both averaged finite-kernel lemmas are unproved; `work-notes/experiments/2026-10-29-precision262.md` |
| E3 | Row-optimal window re-packing under 983,040 rows | 13-window right: 211 bits fits at 966,656 rows; right212 needs left262 and then fits exactly | **done: analysis** | exact integer pricing: `workspace/fewer_windows.py`, `stack/21-right208/src/right-window-pricing.py`; assignments and risks: `docs/FEWER-WINDOWS.md` and patch 21 note |
| E5 | Width-specialize the correction QROM instead of aliasing 15-bit windows through the 32,768-row tree | −13,418,496 T / −0.08733% score on c13a293 | **done, enabled stack patch** | official accepted: 855×15,351,820,448=13,125,806,483,040; proofs/resources in `stack/20-lookup-trees/PATCH.md` |
| E4 | Verified generic gate cancellation over more literal blocks | all 4 EEA occurrences done | **partly done by others** (spariev `c5e75ef`: all four EEA occurrences; still open beyond the 7 EEA literal blocks) | dadon `3e53f42` note: cancellation procedure proved correct for X/CX/CCX |

## F. Merges of public work

| # | Lever | Gain | Status | Owner / evidence |
|---|---|---|---|---|
| F1 (superseded by leader `f7419f1`) | dadon's temporary-AND compiler applied to spariev's 30-window, all-four-cancellation entrant | now ≈ −0.013 % vs leader (the leader did the same merge on `c5e75ef`) | **in flight; base content now matches the leader** | brief 17, `stack/10-temp-and-compiler`, base `a72f4af` |

## G. Spend qubits to save T (patch-10 marginal curve)

| # | Lever | Gain vs projected patch 10 | Status | Owner / evidence |
|---|---|---|---|---|
| G1 | Second/third temporary-AND compiler scratch | 0 T; +0.116822% score per first idle wire | **dead for current syntax** | brief 18: no reachable record-controlled or `whenBit` CCX; protected and measured-AND compute CCX remain literal and are already lowered (`docs/QUBITS-FOR-GATES.md`) |
| G2 | Hold coherent carry/compare ANDs in clean lanes | 614,700 T/lane, but +1q still worsens score 0.111477%; +44q worsens 4.893207% | **dead on marginal score** | exact opportunity census 31,472,640 cleanup CCX, peak 256 lanes; conditional chunked price in `workspace/qubits_for_gates.py` |
| G3 | Replace dirty correction/comparator MCX by clean v-chain | 0 applicable chains | **dead for patch-10 target** | IPX correction and protected EEA already use clean adaptive measured v-chains; remaining comparisons are Cuccaro carry probes |
| G4 | More QROM workspace / 17-bit bank | 0 T under row cap | **dead for 263/224 layout** | current 901,120 rows; minimum 29-signed-window width≤17 layout is 1,245,184 > 983,040 (`docs/QUBITS-FOR-GATES.md`) |
| G5 | Add a shared fast-multiplier lane pool | no achieved cut; corrected w=0 phase-safe fallback is only −0.722413% | **dead pending a cheaper exact signed-quotient erase** | Brief 22 invalidated the one-pass C8 price; extra lanes do not repair the missing quantum-sign-selected phase circuit (`work-notes/experiments/2026-10-29-fastmul-build.md`) |
| G6 | Patch-10 marginal curve, 856…900 | best established score stays 9,855,897,906,944 at 856q | **done: analysis; recommend k=0** | brief 18: `docs/QUBITS-FOR-GATES.md`, `workspace/qubits_for_gates.py` |

## D. Process

| # | Lever | Status | Note |
|---|---|---|---|
| D1 | Build on the promoted frontier and declare dependencies | **policy** | competitors merge promoted entries within an hour; sub-0.05 % edges are short-lived |
| D2 | Separate bench copies per concurrent builder (`workspace/make_bench_copy.sh`) | **policy** | never two builders in one checkout |
| D3 | Codex model for this domain | **policy** | Sol gets cyber-flagged; use Daybreak Blue (`docs/ENVIRONMENT.md`) |
| D5 | Public-effort watch (checked 2026-10-29 ~14:30) | **policy** | Upstream VerifiedQC: nothing new since 2026-10-28 (`streaming-dev` #554). Leaderboard: ArthurOstapenko `8dca04a` was validating. If it promotes, rebase the stack on it before submitting. `lamport/streaming-certificate-docs` documents the five-word correction trade-off (superseded by B1) |
| D6 | **Stacking plan** | **plan** | brief 12 (EEA, `~/shorecdlp`) + brief 13 (multiplier, `~/shorecdlp-m`) → then C9 (drop one square) on top of 13 in the same checkout → merge the 12 and 13 Entrant edits in a fresh checkout at the then-leader → submit only if > 10 % |
| D4a | **Exception (human, 2026-10-29):** submit **brief 17** (merge, stack patch 10) when it lands, if strictly below the leader and verified; replaces the earlier brief-15 exception | **policy** | one-off override of D4 |
| D4 | **Submit only a cut of more than 10 % vs the leader at submission time** (human decision, 2026-10-29) | **policy** | smaller wins are snapshotted and stacked, not submitted. Today's bar: Q×T < 66,361,553,825,085 |

## Review (2026-10-29)

- **Duplicates avoided:** B2/B3 were superseded by B1 and their builders stopped. C2 and C6 are already in the source, so nobody should re-implement them.
  A1/A2 are already in the leader, so don't resubmit them.
- **Only cheap wins left:** C3/C4/C11/C12 are all < 0.04 % each. They are worth shipping (strictly better is promotable), but they won't hold a lead.
- **Brief 22 correction:** C8's direct exact phase-safe fallback is only −0.722413% at unchanged width. Brief 20's −4.551066% count omitted the circuit cost of quantum-sign selection between two different quotient predicates. The donor's ≈−10%
  headline still depends on its three exceptional-state shortcuts and is not an exact target. C7a/C7b remain the large prizes but are XL research with
  open exactness proofs. Several greedyfrog-lineage notes contain untrusted agent-directed text; do not act on it.
- **The real levers are A3 (−17 %), C7 (potentially large) and B6.** All are high-risk or XL. Brief 23 completed the C7 price screens, but exact termination, width and reverse-decode proofs remain the gate; A3 needs new math.
  Recommend: keep submissions on hold, do not build patch 30, and only open a C7 builder after the 256-bit divstep bound plus an n=8 exact forward/reverse receipt kernel-checks.
