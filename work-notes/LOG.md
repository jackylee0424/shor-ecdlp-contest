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

## 2026-10-29 12:15 — Codex — Brief 08: uniform acceptance / rounds6 accepted

- Proved our new secret-uniform per-round acceptance ≥546/1000 in `workspace/AcceptanceCheck.lean` using only protected imports. Analytic route: exact double-cosine expansion of the finite squared amplitude, global cosine lower polynomial of degree six, exact difference/centered moments through degree six, and nonnegative finite-size corrections. Both marginal permutations are proved; `uv≥u+v−1` needs no independence assumption. Mathlib bounds are named `Real.pi_gt_d6` / `pi_lt_d6` in this checkout.
- Main lemmas: `ShorECDLP.Acceptance.geometric_sextic`, `polynomial_marginal`, `average_peak_sextic`, `coverage_of_average`, `secpCoverage_546`, `secpVerified_546`. Exact rational arithmetic gives marginal ≥7731/10000, then pair ≥546/1000 after dropping character zero. Protected physical/decoder equalities feed this into the actual streaming round. Six retries certify success ≥0.9912434079546311.
- Extended `workspace/port_upstream.py --rounds N` to compute resource totals for N=1–56. New `workspace/apply_uniform_acceptance.py` installs the contribution and replaces the two acceptance interfaces; `package_streaming.py` retains upstream attribution and identifies our theorem as our contribution. Final source consists only of the four existing tracked Entrant files; no protected/other bench sources changed.
- Initial packaged build passed (98s), but first official attempt `logs/score-20261029-120638.log` rejected 16 linter warnings under `lake --wfail`. Removed all causes without suppressing linters. Clean scratch check: ~6s; cleaned packaged build: 60s (`logs/build-20261029-120938.log`); axioms exactly {propext, Classical.choice, Quot.sound}; boundary passed.
- Official `formal-tools/score.sh` **accepted** after 217s (`logs/score-20261029-121115.log`), including fresh warning-failing build and kernel replay (8 Challenge, 1 Judge, 4 Entrant): **3,932 × 86,360,247,846 = 339,568,494,530,472**, measurements **5,163,644,892**. Scored snapshot `entrants/20261029-1215-rounds6`. This is the full requested six-round result, 13/3 better than streaming26.
- Experiment `work-notes/experiments/2026-10-29-uniform-acceptance.md`; SCOREBOARD/HANDOFF and contribution-plan status updated. No submission, push or Git metadata writes by this agent; per brief, no commit attempted.

## 2026-10-29 — Codex — Brief 10 stopped at exact measured-comparator seam

- Checked the flag-only endpoint semantics through the prepared and relabeled actual-window seam: dirty MCX restoration, endpoint source/target injectivity, matching and nonmatching flag schedules, clean exit, `pointWrite` correctness, coherence and conservative exact counts. Preserved modular WIP: `workspace/flag855-wip/`.
- The protected `computeEqConstAdaptive` cleans its v-chain before the dirty half can consume the conjunction. The required 1,276-CCX zero test needs a continuation-aware clean v-chain: 256 forward CCX, the 1,020-CCX dirty MCX, then 256 measurement erasures. The checked fallback is 2,042 CCX/test and uses 24 rather than 13 QROM traversals, so it was not packaged or scored.
- Exact continuation target: generalize the private `mcxVChainTailAdaptive_coherent` with a deepest-node continuation preserving `PathAndComputed`; separately prove a two-column/same-target query leaf to fuse adjacent traversals. Detailed obligations and conservative projections: `work-notes/experiments/2026-10-29-flag855.md`.
- Restored `entrants/20261029-1215-rounds6` byte-for-byte and reran `formal-tools/boundary.sh` successfully. No SCOREBOARD row, snapshot, submit, push or commit.

## 2026-10-29 — Codex — Brief 13 stopped at exact multiplier feasibility gate

- Audited all six Horner and two square call sites on frontier `93051d2`. `workspace/MulClean.lean` kernel-checks the public cleanliness consequences: 68 clean lanes at ordinary Figure-15 multiplier boundaries, 69 at the square boundaries, but only **25** (`4..6`, `558..579`) at three post-forward-EEA calls. The forward EEA output consumes or leaves persistent state in the other candidate lanes; relabeling into the data bank preserves the 25-lane shortfall.
- The requested signed-digit merged-fold design needs about 70 clean lanes (the donor's direct fused table uses 74 pool lanes plus an overflow flag), so the brief's mandatory feasibility gate failed. A 45-wire expansion to 900 qubits cannot meet the >10% policy even with zero-T replacement calls: Q×T=68,212,747,409,400, a 7.489398409% cut.
- `workspace/mul_feasibility.py` gives the exact conditional budget: `T = 75,791,941,566 + 2,408,448*c_bit + 9,408*F`. The strict policy permits at most 757 CCX/bit with 76 fixed CCX/call of slack; 758 CCX/bit misses by 1,447,278,165 score. Full call table, algebra and stacking margins: `docs/MUL-PLAN.md`; experiment: `work-notes/experiments/2026-10-29-mul.md`.
- Per “stop if feasibility fails,” no Entrant file changed. `/home/gitzard/shorecdlp-m` is clean at `93051d2`; no build, axioms/boundary/score run, snapshot, submission, push or commit, and no SCOREBOARD row.

## 2026-10-29 — Codex — Brief 14b: fewer-window single-trial analysis

- Exact protected-decoder audit: one-trial `wrappedShift` first fits the candidate cap at rightBits=203 (`2^54+2` checks); it rounds the left axis once and enumerates numerator ambiguity inside one right output bin, so its right success is a nearest-bin event. The 263/203 resource optimum removes four signed additions and would score 12,699,380,930,760 (−12.120916%), but `d=1` success is only about 0.773695 (analytic upper <0.779), so the >10% projection is not certifiable.
- A character-averaged `nearestPair` lemma at 262/262 has a plausible uniform lower ≈0.993668, but row-optimal packing still needs 33 signed additions and saves only 524 phase T. The first window cut needs 258/258 with width 17 (or 256/256 with widths ≤16), below the success range.
- Derived the exact conditional specialized-lookup law `91*(rows-1)+85848`: 15-bit windows would cost 510,666,415 T after the leader patch versus the current aliased 512,157,359 T. Stacked with 262/262 this projects 855×16,871,901,094=14,425,475,435,370 (−0.176428%), below submission policy. Evidence: `docs/FEWER-WINDOWS.md`, `workspace/fewer_windows.py`; lab-only writes, bench `8513c15` remained clean/read-only; no Lean build, score, snapshot, submission, push or commit.

## 2026-10-29 — Codex — Brief 16 stopped at exact dirty-fold count gate

- Rechecked `workspace/MulClean.lean` on dadon `c6a88fc` / bench `c13a293`: five fast-multiplier sites expose 68–69 clean lanes and the same three post-forward-EEA sites expose only 25. The single-trial entrant has 30 corrected windows and eight 1,110,533-CCX calls/window; a 3% patch requires `5*high + 3*low < 26144.023001 CCX` per recurring cell.
- The ecdsa.fail donor emitted 138,289 Toffolis/product at pool 76 (~540/bit), but inspection confirmed its 64-lane fold, 32-lane flag erase and assumed high bit are exceptional-state approximations. Exact algebra reduces the fused correction to `d+B-q*p`, `q∈{-1,0,1}`; `workspace/FastMulAlgebra.lean` checks the pseudo-Mersenne/signed-digit identities and `workspace/dirtyfold_feasibility.py` checks the fused integer model and projections.
- The proved dirty MCX restores donors, but no existing theorem erases the post-correction quotient flag without reconstructing the full pre-correction word/comparison; the exact worst-case fast-cell count therefore did not exist. Per the gate, no Entrant/stack mutation, build, score, snapshot or SCOREBOARD row. Achieved cut 0%; full record `work-notes/experiments/2026-10-29-dirtyfold-mul.md`. Bench remains clean at `c13a293`; no submit, push or commit.

## 2026-10-29 — Codex — Brief 15: specialized lookup patch accepted; right-window patch parked

- Implemented and enabled `stack/20-lookup-trees`: nine 15-bit signed windows now use proved 14-level/16,384-leaf physical correction trees behind the unchanged 32,768-row coefficient interface. Alias, coherent semantics, counts, T, slots, support, Fourier metadata, decoder cursors, and the leader's cancellation rewrite all compile. Exact cut: 13,418,496 T and 1,916,928 measurements at unchanged 855 qubits.
- Clean-base replay (reverse-applied to exact `c13a293` because sandboxed Git metadata rejected `git reset --hard`, then `apply.sh`) passed build, linter, axioms `{propext, Classical.choice, Quot.sound}`, boundary, protected/Entrant kernel replay, and official score: **855 × 15,351,820,448 = 13,125,806,483,040**, measurements 919,171,864. Logs: `logs/build-20261029-165224.log`, `logs/score-20261029-165313.log`.
- Priced `stack/21-right208` before mutation. A finite residue-strip/kernel bound puts 208-bit combined success below 0.984935; the tighter limiting diagnostics for 208/209/210 are ≈0.966900/0.979870/0.986902, so all fail 99%. Right211 is numerically plausible at ≈0.990690 and 966,656 rows but needs three width-17 trees, another bank wire, and a new averaged finite-kernel Lean proof. Left262/right212 fits exactly 983,040 rows with diagnostic ≈0.994519 but needs two unproved averaged lemmas. Patch 21 has no `ENABLED`; `apply.sh` exits 3.
- Evidence and reproduction: `work-notes/experiments/2026-10-29-precision262.md`, extended `workspace/fewer_windows.py`, both patch `PATCH.md` files, and `stack/21-right208/src/right-window-pricing.py`. Updated SCOREBOARD, HANDOFF, and LEVERS E1b/E2/E3/E5. No submit, push, or commit.
