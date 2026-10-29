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
