# Brief 11 — Option C: dirty-borrowed comparator only (3,932 → ~3,421 qubits), in a SEPARATE bench copy

Read `AGENTS.md`, `work-notes/HANDOFF.md`, `docs/ECDSAFAIL-TRICKS.md` ("Top three" §1) and `briefs/09-compact-correction-qubits.md`
(step 1 only: this brief is that step).

## Critical: your bench is `~/shorecdlp-c`, not `~/shorecdlp`

Brief 10 (another Codex agent) is concurrently editing `~/shorecdlp`. **Never touch `~/shorecdlp`.** Your bench is the independent copy
`/home/gitzard/shorecdlp-c` (same pinned commit, full build cache, Entrant = the accepted `entrants/20261029-1215-rounds6`).
Prefix **every** formal-tools command with `BENCH=/home/gitzard/shorecdlp-c`, e.g.
`BENCH=/home/gitzard/shorecdlp-c formal-tools/build.sh`, `... formal-tools/check.sh`, `... axioms.sh`, `... boundary.sh`, `... score.sh`, `... snapshot.sh`.
Also pass `BENCH` to any lab script that defaults to `~/shorecdlp` (check `workspace/port_upstream.py`, `apply_uniform_acceptance.py`,
`package_streaming.py` for a bench-path argument or variable, and use the copy).

Lab file ownership: brief 10 owns `workspace/Flag*.lean` and may read `workspace/DirtyMCX.lean` / `DirtyBatch.lean`. **Do not edit those four files.**
Copy what you need into new files `workspace/C_*.lean`. Append to LOG/HANDOFF/SCOREBOARD; don't rewrite other agents' rows.

## Goal

Replace the 511 clean equality-chain scratch wires (4103–4613) of the batched endpoint correction with a dirty-borrowed multi-controlled X
(donors: endpoint-word/accumulator wires that are not controls or the target of that test). Keep the five endpoint words and everything else as upstream has them.
- Prove the dirty chain implements MCX for arbitrary donor/control/target values, restores donors, leaves no phase garbage, is well formed,
  and costs 4(k−2) CCX (brief 09's drafts in `workspace/DirtyMCX.lean`/`DirtyBatch.lean` are a starting point; copy, don't edit).
- Re-prove the equality flag action and `endpointTransposition_correct` with the replacement; preserve `batchModel_data` / `batchModel_clean`.
- Rebuild the correction builder, reset list, support (`BatchSupport`, `CompleteSupport`), counts/stride, positions/layout, `UniformT`, and the resource
  assembly. The removed labels must be absent from every reset and window.
- Expected: about **3,421 qubits**, T about +0.089 % per round (≈ 86.44e9 total), **Q×T ≈ 2.95e14**. Recompute exactly.

Develop modularly, package into the four tracked Entrant files (source policy), then
`BENCH=/home/gitzard/shorecdlp-c formal-tools/{build,axioms,boundary,score}.sh`, then `... snapshot.sh dirty3421 "<score>"`.

## Record

Experiment note `work-notes/experiments/2026-10-29-dirty3421.md`, a SCOREBOARD row, and LOG/HANDOFF lines. Credit: dirty-borrowed comparator technique from
our ecdsa.fail low-qubit work; construction upstream VerifiedQC (keep the `Main.lean` attribution). Do not submit, push, or commit.
