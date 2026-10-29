# Brief 10b — integrate the CONSERVATIVE flag-only correction to a scored 855-qubit entrant

Read `AGENTS.md`, `work-notes/HANDOFF.md`, `briefs/10-flag-only-correction-855q.md` and **`work-notes/experiments/2026-10-29-flag855.md`**
(Brief 10's result). Checked work-in-progress: `workspace/flag855-wip/` (README inside).

## Decision (orchestrator, overriding Brief 10's "exact only")

**Integrate the checked conservative prototype now.** It has 24 single-column traversals and the unitary split comparator (2,042 CCX/test), with a
projected **855 × 86,668,498,614 = 74,101,566,314,970**. That is only 0.5 % more T than the exact design, and 4.6× better than the current leaderboard best
(339,568,494,530,472). A scored 855-qubit entrant first; the exact 13-query / 1,276-CCX optimization is a later, separate brief. Do **not** stop to
chase the exact comparator or the paired-column query.

## Bench

`~/shorecdlp` (restored to `entrants/20261029-1215-rounds6`; Brief 10 is finished). **Do not touch `~/shorecdlp-c`** (Brief 11 is running there)
or `~/shorecdlp-a`. Don't edit `workspace/C_*.lean`.

## Remaining work

Starting from `workspace/flag855-wip/` (`Pipeline.lean` already checks the prepared/relabeled actual-window coherence seam and defines an 854-wire
reset plan; `Counts.lean` has the exact conservative counts):
1. Replace the old batched window by the flag window in the round/outer plan (Entrant terms only; protected files untouched).
2. Redo records/stride, decoder positions/layout, `UniformT`, gate slots, the support lemmas (`CompleteSupport` → **855**, no label ≥ 1024, including
   the reset list) and the resource assembly. Keep the 6-round acceptance chain (our uniform ≥ 546/1000) unchanged.
3. Recompute `streamingBounds` exactly from the checked counts (expected T 86,668,498,614; records ≈ 6 × stride; recheck the cap 47,471,340,504).
4. Package into the four tracked Entrant files (`workspace/package_streaming.py`, extended as needed), then `formal-tools/build.sh`,
   `axioms.sh`, `boundary.sh`, `score.sh`, `snapshot.sh flag855 "<score>"`. Fix linter warnings (the official build uses `--wfail`).

If a step blocks, keep going on the rest and report the exact blocking obligation (module, statement, attempts). Leave the bench at rounds6 if
you cannot finish. Record: experiment note (append to `2026-10-29-flag855.md`), SCOREBOARD row, LOG, HANDOFF. Keep the upstream attribution in
`Main.lean` and add a line for our flag-only correction. Do not submit, push, or commit.
