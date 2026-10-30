# HANDOFF — read this first, update it last

_Last updated: 2026-10-29 by Codex (Brief 21 complete: the 855-wire EEA peak has no free owner; the only exact 854-wire fallback worsens score 32.38%. Concurrent Briefs 17/19 remain in flight)._

## Current best

| Candidate | Qubits | T-model | Q×T | Verified how |
|---|---|---|---|---|
| leader spariev f7419f1 | 855 | 11,512,613,384 | **9,843,284,443,320** | bench commit `5d39a5f`; Brief 21 source/certificate audit |
| historical dadon bcad5b2 | 856 | 12,747,275,522 | **10,911,667,846,832** | bench commit `7bc69a7` |
| c13a293 + stack patch 20 | 855 | 15,351,820,448 | **13,125,806,483,040** | official benchmark accepted; 919,171,864 measurements; `stack/20-lookup-trees` |
| frontier dadon c6a88fc | 855 | 15,365,238,944 | **13,137,279,297,120** | bench commit `c13a293`; Brief 16 base, boundary unchanged |
| frontier ff1bf8d | 855 | 86,239,836,030 | **73,735,059,805,650** | frontier commit `93051d2`; reproduced before Brief 13 |
| rounds6 (current bench Entrant) | 3,932 | 86,360,247,846 | **339,568,494,530,472** | official benchmark accepted, full kernel replay, 217s; `entrants/20261029-1215-rounds6` |
| streaming26 (previous accepted entrant) | 3,932 | 374,227,740,666 | **1,471,463,476,298,712** | official benchmark accepted, full kernel replay, 232s; `entrants/20261029-1149-streaming26` |
| shipped Entrant (bench HEAD 535a493) | 206,642 | 355,060,161,799,520 | 73,370,341,954,576,411,840 (≈7.34e19) | `yukon run` accepted 2026-10-29 (snapshot `entrants/20261029-1111-baseline`) |

## State of the environment

- The lab scaffold exists (this repo). The bench is cloned in WSL `gitzard-formal` at `~/shorecdlp`.
- `yukon setup --track lean` completed 2026-10-29 (3,514 jobs). Bench fully built.
- `~/shorecdlp` is clean at HEAD `5d39a5f` (spariev `f7419f1`) for Brief 21.  The sandbox could not rewrite Git metadata, but no reset was needed because HEAD and Entrant already matched the requested commit.  Reapply patch 20 from a clean compatible leader with `BENCH=/home/gitzard/shorecdlp stack/20-lookup-trees/apply.sh`.
- Codex sub-agents (`gpt-6.1-sol`) work via `formal-tools/codex-agent.sh`.

## In flight

| Agent | Since | Item | Output location |
|---|---|---|---|
| Codex | 2026-10-29 | Brief 19: port patch 20 width-specialized lookup trees onto dadon's temporary-AND compiler program; validate exact compiler-aware resources on `3fbf1a8` | `stack/20-lookup-trees/`; `/home/gitzard/shorecdlp/…/Entrant/` |
| Codex | 2026-10-29 | Brief 17: merge dadon `bcad5b2` temporary-AND compiler onto spariev `070b740` as stack patch 10; verify and score on bench `shorecdlp-m` | `stack/10-temp-and-compiler/`; `/home/gitzard/shorecdlp-m/…/Entrant/` |
| Codex | 2026-10-29 | Brief 10b: integrate and score conservative flag-only correction, target 855 qubits | `workspace/flag855-wip/`; `/home/gitzard/shorecdlp/…/Entrant/` |
| Codex (Option C) | 2026-10-29 | Brief 11: dirty-borrowed comparator only, target 3,421 qubits; separate bench `/home/gitzard/shorecdlp-c` | workspace/C_*.lean; `/home/gitzard/shorecdlp-c/…/Entrant/` if accepted |
| Codex | 2026-10-29 | Brief 12: exact EEA inversion-wrapper inventory, then first exact T-cut on frontier ff1bf8d | `workspace/eea_inventory.py`; `docs/EEA-INVENTORY.md`; bench Entrant if proved |

## Next up (unclaimed)

- Brief 21 is complete.  At the binding EEA phase, 580 EEA roles + the 256-bit
  data bank + root 836 + infinity 838 + the 16-wire address/sign bank + compiler
  ancilla 1024 occupy all 855 owners.  Apparent idle lookup/IPX roles are physical
  EEA owners then.  The only current-source one-wire cut is the unlowered Parent:
  **854×15,258,353,144=13,030,633,584,976**, +32.380951297%.  Any competitive
  854-wire redesign must add at most 13,480,811 T (2,696,162 compiled 5T-CCX).
  Existing sharing/borrowing/MBU/address reuse is already applied; packed rings,
  spooky recomputation and v3's 835-wire layout need a new EEA and exact proof.
  Recommendation: no stack patch.  Full lifetimes, every q=855…800 threshold and
  technique verdict: `docs/FEWER-QUBITS.md`; calculator:
  `workspace/fewer_qubits.py`; LEVERS B6/B8--B10.  No bench edits or builds.

- Brief 20 supersedes Brief 16's exact-count blocker at the feasibility level. Canonicalise
  the signed add before double/halve: the add/sub quotient is recoverable from the corrected
  output and surviving addend, while the odd-modulus doubling quotient is the output LSB.
  One flag plus a 24-lane exact chunk schedule fits all three 25-lane sites. At w=0 the
  exact construction counts 5,390,896 CCX/window and projects
  **856×10,989,894,224=9,407,349,455,744**, −4.551066% vs patch 10 and
  −4.563488% vs the brief's leader. Every w=1…64 scores worse; recommend **w=0**.
  Full implementation is XL and below the >10% policy. Evidence:
  `docs/FAST-MUL-FEASIBILITY.md`, `workspace/fastmul_feasibility.py`,
  `workspace/FastMulFlag.lean`; LEVERS C8/G5. Bench remained read-only; no Entrant,
  build, score, snapshot, submission, commit or SCOREBOARD row.

- Brief 18 is complete. Against projected patch 10
  **856×11,513,899,424=9,855,897,906,944**, the established at-most-qubit
  frontier stays at 856 qubits through a 900-qubit budget. A hypothetical held-carry
  lane saves only 614,700 T versus 13,435,122 T required for the first extra wire;
  +44 lanes worsen score 4.893207%. The target has no residual conditional CCX class,
  dirty correction MCX, or row-cap-feasible 17-bit window cut. Only the blocked C8
  multiplier pays: at 540 CCX/bit, +45 wires/901 qubits would conditionally cut score
  5.409124%, with break-even 631,319 CCX/call. Recommendation: **build k=0** until
  C8 has an exact circuit/count. Evidence: `docs/QUBITS-FOR-GATES.md`,
  `workspace/qubits_for_gates.py`; LEVERS G1–G6. No bench edits or builds.

- Brief 15 is complete. `stack/20-lookup-trees` is enabled and officially
  accepted on `c13a293`: nine specialized 15-bit correction trees save exactly
  13,418,496 T and 1,916,928 measurements, yielding
  **855×15,351,820,448=13,125,806,483,040**. Clean-base apply/build/axioms/
  boundary/score replay passed; proof and resource anchors are in its
  `PATCH.md`. `stack/21-right208` is parked (no `ENABLED`): 208–210 physical
  right bits fail success, while 211 bits and left262/right212 are only
  numerically plausible and still need averaged finite-kernel Lean proofs plus
  width-17 physical trees. Full record:
  `work-notes/experiments/2026-10-29-precision262.md`.

- Brief 16 stopped at the single-trial exact-count gate. `workspace/MulClean.lean` still
  proves 68–69 clean lanes at five calls and only 25 at three calls on `c13a293`. The
  exact 30-window 3% condition is `5*high + 3*low < 26144.023001 CCX` per recurring cell.
  The donor's measured ~540-CCX/bit headline is ineligible: it truncates the fold and flag
  comparisons. The exact fused quotient is only `q∈{-1,0,1}`, but its post-correction flag
  lacks a proved narrow phase-safe erase; using the full word reconstruction removes the
  priced gain. Evidence: `workspace/FastMulAlgebra.lean`,
  `workspace/dirtyfold_feasibility.py`, `docs/MUL-PLAN.md`, and
  `work-notes/experiments/2026-10-29-dirtyfold-mul.md`. Achieved patch cut 0%; no stack
  directory, score, snapshot, submission or commit. Bench is clean at `c13a293`.

- Brief 14b supersedes Brief 14 and is complete: `wrappedShift` first fits at rightBits=203 and
  its 263/203 packing removes four signed additions (resource-only score 12,699,380,930,760), but
  its one-bin right event caps `d=1` success near 0.773695, so it is dead for a single 99% trial.
  A 262/262 averaged `nearestPair` proof is plausible at ≈0.993668 but removes no window; stacked
  with specialized 15-bit lookup trees it is only −0.176428%. Full accepted-set, row assignments,
  exact T formulas and proof-risk table: `docs/FEWER-WINDOWS.md`; calculator:
  `workspace/fewer_windows.py`. No bench/build/score/snapshot/submission/commit.

- Brief 13 stopped at its mandatory feasibility gate. Three of the eight replacement sites
  (`division multiply-to-work`, `multiplication recompute`, `multiplication unrecompute`) expose
  only **25** proved-clean lanes outside the destination after the forward EEA; ordinary multiply
  sites have 68 and square sites 69. The requested modp_ft-style cell needs about 70 (the donor's
  direct fused table is 74 pool lanes plus a flag). Kernel-checked inventory:
  `workspace/MulClean.lean`; exact projections: `workspace/mul_feasibility.py`; full analysis:
  `docs/MUL-PLAN.md` and `work-notes/experiments/2026-10-29-mul.md`. Reopen C8 only with a
  ≤25-clean-lane exact cell, dirty-borrowed restoration, or an EEA/layout change freeing ≥45
  lanes at unchanged support. At 855 Q the strict policy envelope is ≤757 CCX/bit with at most
  76 fixed CCX/call; 758 CCX/bit misses by 1,447,278,165 score. Adding 45 qubits fails even if
  all eight calls become free. `/home/gitzard/shorecdlp-m` remains clean at `93051d2`; no build,
  score, snapshot, submission, push or commit.

- Brief 10 flag855 WIP is preserved in `workspace/flag855-wip/`; full findings are in
  `work-notes/experiments/2026-10-29-flag855.md`. Endpoint logic, pure flag action, concrete
  state refinement, all-valid-input `pointWrite`, window coherence and the prepared/actual
  seam check. The exact blocker is the 1,276-CCX split zero test: generalize the private
  `mcxVChainTailAdaptive_coherent` with a deepest-node dirty-MCX continuation, then unwind
  256 conjunctions with measured erasure. Also fuse adjacent endpoint columns into one
  Clifford leaf to reduce 24 traversals to 13. Do not integrate the checked conservative
  fallback (2,042 CCX/test); it projects 86,668,498,614 T and misses the brief. Bench is the
  byte-identical accepted rounds6 snapshot; no new score or SCOREBOARD row.

- Brief 07 complete: `docs/ECDLP-AI-GOLD.md` inventories Gold/ecdlp routes, source→Straight design and conditional architecture/error budgets; calculators/index in `workspace/gold_{costs,route_inventory}.py` and `gold_artifacts.json`. **Exact** 2841/2820 line exists (sealed2820), but no inspected full channel/total-point theorem. Small routes remain approximate with unproved uniform failure bounds; 1401/1402 resource lemmas use forbidden native axioms. Start with one exact source-bound Gold AND/carry cell → Straight + kernel coherent run/count/support/record theorem, then parametric adder and replay scaling. No bench/donor edits or builds; no new entrant/score.

- Brief 06 complete: `docs/ECDSAFAIL-TRICKS.md` catalogues 23 tricks across all 24 requested entries; `workspace/ecdsafail_tricks_costs.py` checks archived score products and small exact gate identities. New concrete proposal: replace correction equality clean chains with dirty-ancilla MCX borrowing the other endpoint, removing 511 labels for +12,807,424 T/round (3421 Q, projected Q×T 1,281,372,269,953,490). With Brief 05's 310 loans: 3111 Q, projected 1,165,258,442,509,590; both await Lean integration. Binary 464-add/26-round architecture has conditional estimates only: no inspected fast entry proves exact total addition, and control/exception/record budgets can erase the headline gains. Bench and external repos remained read-only; no builds, score or submission.

- Brief 05 complete: `docs/CONTRIBUTIONS-PLAN.md` ranks the next contributions and specifies two implementation outlines.
  Uniform Fourier-peak/moment proof is now implemented and accepted by Brief 08 (p≥0.546 → six rounds); explicit correction-only
  scratch reallocation reaches 3,622 Q (semantic proof pending), combined conditional Q×T=312,796,817,698,212.
  Scripts: `workspace/round_mass.py`, `workspace/streaming_t_breakdown.py`. Existing 16/π⁴≈0.164255716 still needs
  26 rounds; ~870 Q requires a new correction algorithm, not just label reuse. EEA is 86.661% of T. Bench untouched.

1. (done) Baseline scored: accepted, 1m45s warm `yukon run`.
2. Completed Brief 02 map: `docs/CODEBASE-MAP.md` covers 345 important modules, including all protected migration modules.
3. Completed Brief 02 resource audit: `docs/BASELINE-BREAKDOWN.md`; `python3 workspace/baseline_breakdown.py` prints
   exactly 206642 and 355060161799520. Inversion is 99.707% of T; dense-wire bound has 768 sparse-layout holes
   (205874 is an analytical upper bound, not a new certificate). Bench remained unchanged; no new score/replay.
   At that point legacy streaming had a separate 854-wire/800005504760-T contract; Brief 04 now supplies
   the unconditional migrated certificate described below, within the original measurement cap.
   Lab commit could not be created: `.git/index.lock` creation failed with “Read-only file system”; outputs remain
   on disk for the orchestrator to commit. No bench changes or submission were attempted.
4. Brief 04 completed the upstream streaming migration and 26-round certificate. Brief 03's partial work is
   superseded and preserved in `entrants/20261029-1133-brief03-partial` and `docs/MIGRATION-PLAN.md`.
   Briefs 05/06 are quantifying further levers; coordinate with those in-flight tasks. The reset list has
   3,931 wires, while the stronger existing symbolic success bound still cannot certify 25 rounds.
5. First prior-work arithmetic transfer: exact AND-erase / phase-only carry cell using bench measurement-uncompute
   lemmas, then a source-bound measured adder with kernel count/support/record proofs. Native `bv_decide` pilot axioms
   are inadmissible; keep them as research vetoes only. Defer a complete Lilypad/Gold replacement until its control,
   coherent table selection and uniform-error obligations are priced. Survey and calculator are complete:
   `docs/RELATED-WORK.md`, `workspace/related_work_costs.py` (prior repo and bench were read-only).

## Open questions for the human

- Submit cadence: submit each improvement, or only big jumps? (Default: ask before every `yukon submit`.)

## Current Entrant and reproduction (Brief 08 complete)

- **Full requested result accepted:** uniform round acceptance ≥546/1000; `streamingRounds := 6`;
  six-retry success ≥0.9912434079546311; **3,932 Q × 86,360,247,846 T = 339,568,494,530,472**;
  measurements **5,163,644,892**. Snapshot: `entrants/20261029-1215-rounds6`. No submission.
- Our contribution is the acceptance proof. Upstream VerifiedQC construction/reset/retry proofs and attribution
  remain intact. Final form is still only four existing tracked files, including our proof in `WindowMass.lean`.
- Main new theorem: `ShorECDLP.Acceptance.secpCoverage_546` (all nonzero d modulo order), then
  `secpVerified_546`. Exact double-cosine expansion and global degree-six cosine lower bound replace
  the suggested sinc comparison; centered and difference moments through degree six are proved symbolically.
  Both residual marginals are permutations; no independence assumption is used. The finite-size corrections
  are nonnegative. `DecoderBridge.wrappedIdeal_mass_lower` / `FinalCertificate` now use 546/1000.
- Scratch `workspace/AcceptanceCheck.lean` imports only protected modules and checks in ~6s.
  Components `Acceptance{Analytic,Taylor,Moments,Residues,Peak,Mass,Sextic,Bridge}.lean` are assembled by
  `workspace/acceptance_check.py`; exact algebraic moment proofs are generated by `acceptance_moments.py`.
  `AcceptanceQuadratic.lean` preserves the superseded compiling quadratic intermediate.
- Reproduce: `python3 workspace/port_upstream.py --rounds 6`, then
  `python3 workspace/apply_uniform_acceptance.py`, then `python3 workspace/package_streaming.py`.
  The port accepts N=1–56 and computes T/measurements from unchanged per-round counts. It overwrites copied
  modules: apply our contribution before packaging. Restore the scored snapshot for a byte-identical result.
- Build **60s**, no warnings; source gate **631 reachable files**; axioms exactly `propext`, `Classical.choice`,
  `Quot.sound`; boundary passed; official benchmark/full kernel replay **217s**, accepted.
  Logs: `logs/build-20261029-120938.log`, `logs/score-20261029-121115.log`. The first official attempt
  rejected lint warnings under `lake --wfail`; those were fixed without suppressing linters.
- Experiment: `work-notes/experiments/2026-10-29-uniform-acceptance.md`. Remaining width/arithmetic
  contributions from Briefs 05–07 can now be stacked on this six-round entrant. Bench HEAD/protected sources
  are unchanged. This agent did not submit, push, commit, or write Git metadata, as required by the brief.

## Previous accepted entrant and reproduction (Brief 04; historical)

- Upstream construction/proofs: VerifiedQC/ShorECDLP `lamport/challenge-final-certificate` @
  `b46e3371587f2f947c833b665b2636a863b7d85f` (Apache-2.0). The entry, 26-trial decoder and proofs share
  `streamingRounds := 26`. Per-round acceptance ≥ 0.163 gives success ≥ 0.990208214125.
- Accepted measurements: **22,375,794,532**, below the unchanged official 47,471,340,504 cap.
  Certificate axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. Build, source gate,
  boundary, protected replay (8 Challenge + 1 Judge), Entrant replay (4 modules), and final judge all pass.
- **Source-policy constraint:** the checker requires every Lean source to be Git-tracked and reachable.
  Because Git writes are prohibited, the 71 upstream modules plus `Rounds.lean` are packaged into the
  four existing tracked files `Trial.lean`, `Success.lean`, `WindowMass.lean`, `Main.lean`.
  These files now contain streaming proofs. Public namespaces/names stay unchanged; private helpers
  receive module-specific names, and sections preserve each original module's local options/attributes.
- Reproduce from the upstream ref: `python3 workspace/port_upstream.py --rounds 26`, then
  `python3 workspace/package_streaming.py`. This removes the untracked modular `Streaming/` tree.
  Or restore `entrants/20261029-1149-streaming26/Entrant` with the existing restore tool.
  The modular development tree remains in `entrants/20261029-1140-streaming26-modular` (unscored).
- Warm packaged build: 108s; official `formal-tools/score.sh`: **232s**, including a fresh rebuild.
  Logs: `logs/build-20261029-114234.log`, `logs/score-20261029-114434.log`.
  Detailed findings and further levers: `work-notes/experiments/2026-10-29-streaming26.md`.
- Bench HEAD remains `535a493f520dd7efe8c1cfc0b8b5a2741d5b35c1`; protected sources match `origin/master`
  `5fbad2ca7d821393335fb7e659b4f62d30093a02`. Only four Entrant source files differ. No `.git` writes,
  commit, push, or submission were attempted; lab outputs are ready for the orchestrator to commit.
