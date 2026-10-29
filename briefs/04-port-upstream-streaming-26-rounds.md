# Brief 04 — port the upstream streaming certificate into Entrant, cut to 26 rounds

Read `AGENTS.md` and `work-notes/HANDOFF.md` first. The bench is `~/shorecdlp`, fully built, and its protected tree
is identical to the current Yukon frontier (`origin/master` 5fbad2c), so Entrant is the only thing that differs.

## Situation (verified by the orchestrator, 2026-10-29)

- Leaderboard best is 7,243,285,108,034,080,000 (77,624 qubits × 93,312,443,420,000 T; Naive-derived V2 arithmetic).
- Upstream VerifiedQC/ShorECDLP branch `lamport/challenge-final-certificate` (commit `b46e337`, Apache-2.0) proves
  `streamingEntry_certificate_unconditional : Certificate officialLimits batchedOuterPlan.layout streamingEntry streamingBounds`
  with `streamingBounds = ⟨3932, 806028979896, 48194018992⟩`, i.e. 56 rounds.
- The bench already has that branch as a git remote ref: `upstream/lamport/challenge-final-certificate`
  (read it with `git -C ~/shorecdlp show upstream/lamport/challenge-final-certificate:<path>`).
- Relative to the bench, that branch **adds 71 new Lean files** under `ShorECDLP/Submission/2607_13816/` (all `A`, no
  modifications to existing files; listed by `git diff --name-only --diff-filter=A origin/master upstream/lamport/challenge-final-certificate`).
  It also changes protected `ShorECDLP/Challenge/Official.lean`: `measurements := 50000000000`. **The bench keeps 47,471,340,504**,
  so at 56 rounds (48.19e9 measurements) the certificate fails `recordBudget` here.
- No forbidden tokens appear in the 71 files (checked: sorry/admit/axiom/opaque/unsafe/partial/native_decide/bv_decide/extern/implemented_by).
- `streamingRound_success` gives per-round accepted mass ≥ 163/1000. Since 1 − (837/1000)^26 = 0.990208 ≥ 0.99, **26 rounds suffice**.
  Per round, T = 14,393,374,641 and measurements = 860,607,482 (exact quotients of the 56-round bounds).
  At 26 rounds: T ≤ 374,227,740,666, measurements = 22,375,794,532, qubits ≤ 3932, **Q×T = 1,471,463,476,298,712**.

## Goal

A certified Entrant that the local official benchmark accepts with `qubits=3932, tModel=374227740666` (or better).

## Steps

1. Copy the 71 added files into `~/shorecdlp/ShorECDLP/Submission/Entrant/Streaming/` (keep the relative structure under
   `2607_13816/`, e.g. `.../2607_13816/Challenge/FinalCertificate.lean` → `Entrant/Streaming/Challenge/FinalCertificate.lean`).
   Rewrite imports **only for the copied modules**:
   `ShorECDLP.Submission.«2607_13816».<Rest>` → `ShorECDLP.Submission.Entrant.Streaming.<Rest>`. Imports of modules that already
   exist in the bench stay as they are (protected, unchanged). Keep the Lean namespaces as-is; the new declarations do not exist in the bench.
   Write the copy step as a script in the lab (`workspace/port_upstream.py`) so it can be re-run when upstream moves.
2. Build the copied modules bottom-up with `formal-tools/build.sh ShorECDLP.Submission.Entrant.Streaming.Challenge.FinalCertificate`
   (log the wall time). At this point it should compile unchanged except for anything that depends on `officialLimits.measurements`
   (the 56-round record budget proof will fail against 47,471,340,504; that is expected).
3. Change the round count from 56 to 26 in the 8 files that use it (`FinalCertificate`, `FixedWord`, `RepeatEvent`,
   `ResourceCertificate`, `UniformT`, `WindowBudget`, `WindowCounts`, `WindowSlots`). Prefer a single `def streamingRounds : Nat := 26`
   with the lemmas stated for it, or for a general `r` where cheap. Re-prove the success step for 26:
   `(99:ℝ)/100 ≤ independentRetrySuccessProbability ((163:ℝ)/1000) 26` (norm_num should handle it). Make sure the decoder layout,
   repeat entry and candidate budget all use the same 26. Update `streamingBounds` to `⟨3932, 374227740666, 22375794532⟩`
   (or recompute it exactly from the per-round lemmas).
4. Rewrite `Entrant/Main.lean` to export `entry`, `layout`, `bounds` and `certificate` from the streaming construction. Delete the
   old Naive-derived entrant files (`Trial.lean`, `Success.lean`, `WindowMass.lean`) if nothing imports them; the old entrant is
   preserved in `entrants/20261029-1111-baseline`. Put an attribution header in `Main.lean`: construction and proofs from
   VerifiedQC/ShorECDLP `lamport/challenge-final-certificate` @ b46e337 (Apache-2.0), with the round count reduced 56 → 26 using the
   upstream per-round 0.163 acceptance bound.
5. Verify with `formal-tools/build.sh`, `formal-tools/axioms.sh` (only propext / Classical.choice / Quot.sound),
   `formal-tools/boundary.sh`, then `formal-tools/score.sh`. Then `formal-tools/snapshot.sh streaming26 "<score>"`.
6. If there is time: is 163/1000 the best per-round bound the upstream proof gives? A bigger per-round mass means fewer rounds.
   Note the levers (rounds, reset list of 3,931 wires inflating qubits, per-window T) in `work-notes/experiments/2026-10-29-streaming26.md`.

## Constraints

- Only `~/shorecdlp/ShorECDLP/Submission/Entrant/` may change in the bench. Do not touch `.git` beyond reading it (you cannot commit).
- No `sorry`/`axiom`/`native_decide`/`bv_decide`. Do **not** run `yukon submit`.
- Builds of the copied tree may be slow: run them one module chain at a time and record the times.

## Output

The working Entrant in the bench, plus a snapshot, `workspace/port_upstream.py`, an experiment note, a SCOREBOARD row (if scored), and
LOG + HANDOFF updates. If blocked, write exactly where (module, error, what you tried) in the experiment note and HANDOFF.
