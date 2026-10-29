# Brief 03 — audit the 2607_13816 → Straight migration and plan its completion inside Entrant

Read `AGENTS.md`, `work-notes/HANDOFF.md`, `docs/CHALLENGE.md`, `docs/RELATED-WORK.md` §1 and
`docs/CODEBASE-MAP.md` (sections on `Submission/2607_13816`) first. The bench is `~/shorecdlp` and is fully built.

## Why

The shipped entrant scores ≈7.34e19 (206,642 qubits × 3.55e14 T; Fermat inversion is 99.7 % of T). The bench
already contains a partially migrated streaming construction (arXiv:2607.13816) whose legacy, non-challenge
contract is 854 wires × 8.0e11 T (≈6.8e14). Finishing it inside `Entrant/` is our main route, worth about 1e5× on score.

## Goal (analysis + one concrete proof step; no score claims without a build)

1. **Obligation inventory.** Look at `B/Challenge/CertificateAssembly.lean` (`StreamingAssembly`) and everything
   feeding it (`WindowBody`, `OuterResources`, `Positions`, `SharedTable`, `InPlace`, `GidneyAdd`,
   `RegisterCorrection`, `BatchCost`, ...). List every field or hypothesis that is still **not** instantiated for an actual
   producer. For each, say what already exists in the bench (theorem names), what is missing, and an S/M/L/XL size.
   Use `#print axioms` / `#check` scratch in `workspace/` (run it with `formal-tools/check.sh`) to confirm that key theorems exist and are axiom-clean.
2. **True post-migration costs.** For the current `batchedOuterPlan` (3,931-entry reset list), compute the
   actual support size, T-model and measurements from the source formulas (`workspace/streaming_costs.py`).
   Check them against the official limits, especially the measurement cap of 47,471,340,504, which the legacy design hits exactly.
   If the batched design overflows a limit, find the cheapest change that fits (for example fewer resets, or a different
   correction batching), and price it.
3. **Plan.** Write `docs/MIGRATION-PLAN.md`: an ordered list of milestones, each ending in something that can be
   checked (a compiling lemma in `Entrant/`, or a workspace file), with sizes, risks, and the expected final
   qubits / T / Q×T. Identify the **first milestone** that can be completed in one agent session.
4. **Do the first milestone** if it is S or M sized. Write it under `~/shorecdlp/ShorECDLP/Submission/Entrant/`
   in new files, e.g. `Entrant/Streaming/*.lean`. Leave `Main.lean` exporting the current certified baseline untouched,
   so the bench stays scoreable. It must compile (`formal-tools/build.sh ShorECDLP.Submission.Entrant.Streaming.<Mod>`),
   with no `sorry` and only allowed axioms. Run `formal-tools/boundary.sh`.

## Constraints

- Only `~/shorecdlp/ShorECDLP/Submission/Entrant/` may be modified in the bench; everything else is read-only.
- No `sorry`/`axiom`/`native_decide`/`bv_decide` in anything you add to Entrant.
- You cannot git-commit (the sandbox makes `.git` read-only). The orchestrator commits.

## Output

`docs/MIGRATION-PLAN.md`, `workspace/streaming_costs.py`, any new `Entrant/Streaming/*.lean`, a LOG line,
and an updated HANDOFF ("In flight" cleared; next milestone listed). If you wrote Entrant files, run
`formal-tools/snapshot.sh streaming-m1 "<note>"`.
