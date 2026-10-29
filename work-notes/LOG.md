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
