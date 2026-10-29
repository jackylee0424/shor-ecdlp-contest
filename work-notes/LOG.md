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
