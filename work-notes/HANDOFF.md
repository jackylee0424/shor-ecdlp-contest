# HANDOFF — read this first, update it last

_Last updated: 2026-10-29 by Codex (Brief 10 stopped at exact measured-comparator seam; rounds6 restored)._

## Current best

| Candidate | Qubits | T-model | Q×T | Verified how |
|---|---|---|---|---|
| rounds6 (current bench Entrant) | 3,932 | 86,360,247,846 | **339,568,494,530,472** | official benchmark accepted, full kernel replay, 217s; `entrants/20261029-1215-rounds6` |
| streaming26 (previous accepted entrant) | 3,932 | 374,227,740,666 | **1,471,463,476,298,712** | official benchmark accepted, full kernel replay, 232s; `entrants/20261029-1149-streaming26` |
| shipped Entrant (bench HEAD 535a493) | 206,642 | 355,060,161,799,520 | 73,370,341,954,576,411,840 (≈7.34e19) | `yukon run` accepted 2026-10-29 (snapshot `entrants/20261029-1111-baseline`) |

## State of the environment

- The lab scaffold exists (this repo). The bench is cloned in WSL `gitzard-formal` at `~/shorecdlp`.
- `yukon setup --track lean` completed 2026-10-29 (3,514 jobs). Bench fully built.
- Codex sub-agents (`gpt-6.1-sol`) work via `formal-tools/codex-agent.sh`.

## In flight

| Agent | Since | Item | Output location |
|---|---|---|---|
| Codex (Option C) | 2026-10-29 | Brief 11: dirty-borrowed comparator only, target 3,421 qubits; separate bench `/home/gitzard/shorecdlp-c` | workspace/C_*.lean; `/home/gitzard/shorecdlp-c/…/Entrant/` if accepted |

## Next up (unclaimed)

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
