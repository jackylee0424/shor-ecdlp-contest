# HANDOFF — read this first, update it last

_Last updated: 2026-10-29 by Codex (Brief 02 complete; Brief 01 findings retained)._

## Current best

| Candidate | Qubits | T-model | Q×T | Verified how |
|---|---|---|---|---|
| shipped Entrant (bench HEAD 535a493) | 206,642 | 355,060,161,799,520 | 73,370,341,954,576,411,840 (≈7.34e19) | `yukon run` accepted 2026-10-29 (snapshot `entrants/20261029-1111-baseline`) |

## State of the environment

- The lab scaffold exists (this repo). The bench is cloned in WSL `gitzard-formal` at `~/shorecdlp`.
- `yukon setup --track lean` completed 2026-10-29 (3,514 jobs). Bench fully built.
- Codex sub-agents (`gpt-6.1-sol`) work via `formal-tools/codex-agent.sh`.

## In flight

| Agent | Since | Item | Output location |
|---|---|---|---|
| Codex | 2026-10-29 | Brief 04: port upstream certificate and certify 26 streaming rounds | workspace/port_upstream.py; Entrant/Streaming/; experiments/2026-10-29-streaming26.md |
| Codex | 2026-10-29 | Brief 03: streaming migration audit, cost model and first proof milestone | docs/MIGRATION-PLAN.md; workspace/; Entrant/Streaming/ |

## Next up (unclaimed)

1. (done) Baseline scored: accepted, 1m45s warm `yukon run`.
2. Completed Brief 02 map: `docs/CODEBASE-MAP.md` covers 345 important modules, including all protected migration modules.
3. Completed Brief 02 resource audit: `docs/BASELINE-BREAKDOWN.md`; `python3 workspace/baseline_breakdown.py` prints
   exactly 206642 and 355060161799520. Inversion is 99.707% of T; dense-wire bound has 768 sparse-layout holes
   (205874 is an analytical upper bound, not a new certificate). Bench remained unchanged; no new score/replay.
   Legacy streaming has a proved 854-wire/800005504760-T contract, but protected migration remains open; its
   added correction/reset measurements need fresh accounting against the already-tight official measurement cap.
   Lab commit could not be created: `.git/index.lock` creation failed with “Read-only file system”; outputs remain
   on disk for the orchestrator to commit. No bench changes or submission were attempted.
4. Prioritize an audit/completion plan for the existing `2607_13816/Challenge` producer: actual window/outer execution,
   decoder record correspondence, support and budgets, then instantiate `StreamingAssembly` inside Entrant. The legacy
   854-wire / 8.0e11-T contract is not automatically a migrated challenge certificate; current batched correction has
   a 3,931-entry reset list. See `docs/RELATED-WORK.md` §1 and combine with Brief 02's map.
5. First prior-work arithmetic transfer: exact AND-erase / phase-only carry cell using bench measurement-uncompute
   lemmas, then a source-bound measured adder with kernel count/support/record proofs. Native `bv_decide` pilot axioms
   are inadmissible; keep them as research vetoes only. Defer a complete Lilypad/Gold replacement until its control,
   coherent table selection and uniform-error obligations are priced. Survey and calculator are complete:
   `docs/RELATED-WORK.md`, `workspace/related_work_costs.py` (prior repo and bench were read-only).

## Open questions for the human

- Submit cadence: submit each improvement, or only big jumps? (Default: ask before every `yukon submit`.)
