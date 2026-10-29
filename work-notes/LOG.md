# LOG — append-only; newest at the bottom. Format: `## YYYY-MM-DD HH:MM — agent — title` then bullets.

## 2026-10-29 — Claude Code (Opus 5.5) — lab bootstrap

- Installed the Yukon CLI on Windows and in WSL `gitzard-formal`, and logged in. Cloned the benchmark into WSL `~/shorecdlp`.
- On the human's instruction, the Lean toolchain runs only in WSL `gitzard-formal`. Started `yukon setup --track lean` there.
- Windows Codex sandbox cannot spawn processes, so installed the Linux Codex 0.162.1 in WSL. `CODEX_HOME=~/.codex-wsl` and
  smoke-tested `gpt-6.1-sol` with workspace-write (it can write to the bench).
- Observed that the shipped Entrant is not the Naive baseline: it is a 1-trial, 265-bit-phase variant declaring
  206,642 qubits × 355,060,161,799,520 T.
- Created this lab: AGENTS.md, docs/, work-notes/, workspace/, formal-tools/, entrants/, briefs/.

- 2026-10-29 — Codex — Brief 01 completed: `docs/RELATED-WORK.md` ranks 12 transfers with top-five port sketches, scoped Lean/native-axiom audit and repriced costs (`workspace/related_work_costs.py`); prioritize paper-to-Straight assembly then exact MBU/adders; prior repo and bench remained read-only.

- 2026-10-29 — Codex — Brief 02 completed: 345-module `docs/CODEBASE-MAP.md`, source-cited `docs/BASELINE-BREAKDOWN.md` and `workspace/baseline_breakdown.py` reproduce 206642 qubits / 355060161799520 T / 530 measurements; inversion is 99.707% of T, dense space bound has 768 sparse-layout holes, and legacy 854-wire streaming contracts remain distinct from unfinished protected migration; bench unchanged, no Lean build/score; commit blocked because `.git` is read-only (cannot create index.lock).

## 2026-10-29 — Claude Code (Opus 5.5) — baseline scored

- `yukon setup --track lean` finished (3,514 jobs). `formal-tools/score.sh --yukon` accepted the shipped entrant:
  Q×T = 73,370,341,954,576,411,840 (206,642 × 355,060,161,799,520), 530 measurements, axioms = {Classical.choice, Quot.sound, propext}.
  Warm wall time 1m45s. Snapshot: `entrants/20261029-1111-baseline`.
- Launched Codex brief 03 (streaming migration audit + first milestone).

## 2026-10-29 — Claude Code (Opus 5.5) — leaderboard moved; prior-works inventory

- Leaderboard best is now 7,243,285,108,034,080,000 (`9d15949`, 77,624 × 93,312,443,420,000). Its source is exported to WSL `~/frontier/`.
- Found upstream VerifiedQC `lamport/challenge-final-certificate` @ b46e337: an unconditional streaming certificate (3932 × 806,028,979,896, 56 rounds),
  proved against a raised measurement limit (5e10). Bench limit 47,471,340,504 → cut to 26 rounds (≥ 0.9902) → projected Q×T 1,471,463,476,298,712.
  The bench has git remote `upstream` (local Windows clone). 71 added files, no forbidden tokens. See `docs/PRIOR-WORKS.md`.
- Stopped Codex brief 03 (superseded; partial `Entrant/Streaming/Costs.lean` snapshotted to `entrants/20261029-1133-brief03-partial`, then removed).
- Launched Codex brief 04: port + 26 rounds.

## 2026-10-29 11:49 — Codex — Brief 04: streaming26 accepted

- Ported 71 added Lean modules from VerifiedQC/ShorECDLP `lamport/challenge-final-certificate` @ b46e337 (Apache-2.0), rewriting only copied-module imports. `workspace/port_upstream.py --rounds 26` reproduces the 26-round adaptation, including a shared round count and 26-trial layout. Main exports the unconditional certificate with upstream attribution.
- Unchanged 56-round port build: 101s, expected failure in `WindowBudget` at 48,194,018,992 measurements versus the original 47,471,340,504 cap. Corrected 26-round modular certificate: 13s; Main: 3s. Fixed explicit round-count normalization and retained protected positions in the single-round bridge to avoid a large kernel conversion.
- First benchmark exposed a source-policy constraint: every Lean file must be Git-tracked and reachable; deleting the three old files and adding 72 modular files is rejected. Git writes are prohibited. Preserved modular source in `entrants/20261029-1140-streaming26-modular`; `workspace/package_streaming.py` topologically packages all modules into the four existing tracked Entrant files, scopes local attributes/options, and uniquely prefixes private helper names. No protected source or Git metadata edits.
- Packaged build passed (108s); source gate passed (631 reachable sources); certificate axioms are exactly {propext, Classical.choice, Quot.sound}; boundary passed. Official `formal-tools/score.sh` accepted after a fresh rebuild and kernel replay of 8 Challenge, 1 Judge and 4 Entrant modules (232s): **3932 qubits × 374227740666 T = 1471463476298712**, measurements **22375794532**. Log: `logs/score-20261029-114434.log`.
- Scored snapshot: `entrants/20261029-1149-streaming26` (includes score.json). SCOREBOARD and HANDOFF updated. Experiment: `work-notes/experiments/2026-10-29-streaming26.md`; exact calculator: `workspace/streaming26_counts.py`.
- Stronger upstream per-round symbolic bound is approximately 0.164255716; 25 rounds need approximately 0.168236229, so merely improving the 0.163 rounding cannot reduce rounds. Reset/support and window arithmetic remain the next levers. No submission, push, or commit attempted; read-only Git metadata leaves lab changes for the orchestrator.

## 2026-10-29 — Codex — Brief 05: contribution levers quantified

- Added `docs/CONTRIBUTIONS-PLAN.md` with ranked candidates and two implementation outlines; `workspace/round_mass.py` and `workspace/streaming_t_breakdown.py` reproduce the formulas (~0.3s combined). Upstream/protected code and prior arithmetic were read-only; no bench edits, Lean/lake/build/score, submission or push by this brief.
- Proposed a secret-uniform nearest-peak/moment proof for p≥0.546 (not Lean-checked), enough for six rounds / 86,360,247,846 T. The existing analytic expression is 0.164255716…, which still needs 26 rounds; the true accepted event depends on the secret.
- Explicit correction-only bijection borrows 310 clean arithmetic labels: 3,932→3,622 Q, with boundary/frame/producer proofs pending. Combined conditional six-round score: 312,796,817,698,212. Near-870 width requires a new correction algorithm; naive streamed row comparisons lose on T. EEA wrappers account for 86.661% of round T; already-measured QROM AND cleanup offers no further saving. Measured batch equality cleanup can save 166,659,584 T over 26 rounds with 23,808,512 extra records.
- Experiment record: `work-notes/experiments/2026-10-29-contribution-levers.md`. Incorporated Brief 04's accepted baseline and tracked-source packaging constraint; its in-flight row was not edited. Lab Git metadata is read-only; outputs remain for the orchestrator to commit.

## 2026-10-29 — Codex — Brief 06: ecdsa.fail trick catalogue

- Added `docs/ECDSAFAIL-TRICKS.md`: 23 distinct tricks, all 24 requested archived entry metrics, source/claim qualifications, streaming applicability and proof anchors, binary controlled-public-add architecture with control/exception/measurement costs, and top-three proof plans. `workspace/ecdsafail_tricks_costs.py` reproduces counts, validates 24 score products, exhausts dirty MCX at k=3..6, the five-lane affine bridge, reflection permutations and a small functional dummy-control wrapper. No Lean/build/lake/score/nonce hunt or bench/external-repo writes.
- Concrete exact candidate: borrow dirty endpoint donors for 513-bit equality, replacing 511 clean scratch labels; +12,807,424 T/round, projected 3421 Q × 374560733690 T = 1281372269953490 (1.148× port-relative gain). With Brief 05's 310 loans: 3111 Q, projected 1165258442509590 (1.263×). All producer/coherence/support proofs remain pending. Fast 807–849 and leader entries inherit approximations; no inspected best exact total point-add bound. Binary streaming uses 464 adds/round, 26 rounds and a 7182-T/513-dummy-wire control construction; all proposed full-architecture scores are explicitly conditional, with a ~3.93M-measurement/add ceiling.
- Python calculator and syntax check passed; no benchmark replay. Git metadata is read-only in this agent sandbox; lab changes remain for the orchestrator to commit.

## 2026-10-29 — Codex — Brief 07: ecdlp.ai Gold source-to-Straight audit

- Added `docs/ECDLP-AI-GOLD.md`: 26 route-directory inventory plus distinct Gold Leapfrog epoch11; static-vs-mean counts, shot cohorts, exact/approximate classification, scoped file-level formal evidence and axiom/version qualifications. Exact 2841/2820 line exists, including sealed same-epoch 2820, but no inspected whole-point quantum theorem; 1401/1402 resource proofs expose forbidden `Lean.ofReduceBool`.
- Designed a typed source/IR → Straight backend with explicit nested-guard, mutable-classical-bit, conditional-HMR, physical allocation and kernel replay obligations. M0 recommendation: exact Gold AND/carry cell with normalized coherent run theorem and 7 T / 1 record / 4 slots / 3 wires; no Lean proof claimed by this survey.
- `workspace/gold_route_inventory.py` produces `workspace/gold_artifacts.json` (213 primary/shared/archived formal sources; 71 archived axiom logs). `workspace/gold_costs.py` reproduces conditional 28-window vs 464-controlled-add/26-round budgets and success/error allowances; Python syntax, phase-cell cases, inventory counts, axiom finding and manifest/cost consistency passed. Log: `logs/brief07-gold-costs.txt`. Coordinated final correction/control assumptions with completed Brief06 doc.
- Only lab outputs changed; bench and donor trees read-only, no Lean/lake/build/solver/evaluator/score/submission/push. Git metadata is read-only under the agent sandbox; no commit attempted; outputs are ready for the orchestrator to commit.
