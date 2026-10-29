# HANDOFF — read this first, update it last

_Last updated: 2026-10-29 by Codex (Brief 04 accepted; Briefs 05/06 remain in flight)._

## Current best

| Candidate | Qubits | T-model | Q×T | Verified how |
|---|---|---|---|---|
| streaming26 (current bench Entrant) | 3,932 | 374,227,740,666 | **1,471,463,476,298,712** | official benchmark accepted, full kernel replay, 232s; `entrants/20261029-1149-streaming26` |
| shipped Entrant (bench HEAD 535a493) | 206,642 | 355,060,161,799,520 | 73,370,341,954,576,411,840 (≈7.34e19) | `yukon run` accepted 2026-10-29 (snapshot `entrants/20261029-1111-baseline`) |

## State of the environment

- The lab scaffold exists (this repo). The bench is cloned in WSL `gitzard-formal` at `~/shorecdlp`.
- `yukon setup --track lean` completed 2026-10-29 (3,514 jobs). Bench fully built.
- Codex sub-agents (`gpt-6.1-sol`) work via `formal-tools/codex-agent.sh`.

## In flight

| Agent | Since | Item | Output location |
|---|---|---|---|
| Codex | 2026-10-29 | Brief 06: mine ecdsa.fail low-qubit tricks; bench read-only, no builds | docs/ECDSAFAIL-TRICKS.md; workspace/ecdsafail_tricks_costs.py |
| Codex | 2026-10-29 | Brief 05: quantify support, acceptance and arithmetic levers (bench read-only) | docs/CONTRIBUTIONS-PLAN.md; workspace/round_mass.py; workspace/streaming_t_breakdown.py |

## Next up (unclaimed)

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

## Current Entrant and reproduction (Brief 04 complete)

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
