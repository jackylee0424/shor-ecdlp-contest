# AGENTS.md — research lab for the ShorECDLP Lean 4 challenge

You are one of several coding agents (Claude Code, Codex, others) taking turns on a long-running
formal-methods research effort. **Read this file, then `work-notes/HANDOFF.md`, before doing
anything.** Leave the lab in a state the next agent can pick up from those two files alone.

## Goal

Minimize `score = qubits × tModel` of a Shor ECDLP circuit on secp256k1, with a machine-checked
Lean 4 proof (`ShorECDLP.Challenge.Certificate officialLimits layout entry bounds`) that it
recovers any non-zero secret `d` with probability ≥ 99 %. Lower is better. Rules: `docs/CHALLENGE.md`.

## Two places, one rule

| Place | Path | What lives there |
|---|---|---|
| **Lab** (this repo) | Windows `C:\code\shor-ecdlp-contest`, WSL `/mnt/c/code/shor-ecdlp-contest` | docs, notes, scratch, tools, entrant snapshots. Git-tracked. |
| **Bench** (benchmark checkout) | WSL `gitzard-formal`: `/home/gitzard/shorecdlp` (Windows: `\\wsl.localhost\gitzard-formal\home\gitzard\shorecdlp`) | the official repo; Lean builds; `yukon` commands |

**The rule:** in the bench, edit **only** `ShorECDLP/Submission/Entrant/`. The official checker scans
the real filesystem (untracked and ignored files included) and rejects any other difference.
Never put notes, scratch files, symlinks or helper scripts in the bench. Run `formal-tools/boundary.sh` before scoring or submitting.

The Lean toolchain runs **only inside WSL distro `gitzard-formal`** (do not use a Windows `lake`).
Details: `docs/ENVIRONMENT.md`.

## Lab layout

```
AGENTS.md            this file (CLAUDE.md just imports it)
docs/                stable knowledge: CHALLENGE, ENVIRONMENT, CODEBASE-MAP, STRATEGY, LEAN-TIPS
work-notes/          living state: HANDOFF (read first), LOG (append-only), SCOREBOARD, experiments/
workspace/           scratch Lean files and Python calculators (compiled against the bench)
formal-tools/        scripts: check, build, axioms, boundary, score, snapshot, restore, codex-agent
entrants/            snapshots of Entrant/ trees, one dir per candidate (with score.json if scored)
briefs/              task briefs handed to sub-agents (keep them; they document intent)
logs/                tool output (gitignored)
```

## Working loop

1. Read `work-notes/HANDOFF.md`, skim the tail of `work-notes/LOG.md`, and check `work-notes/SCOREBOARD.md`.
2. Pick or claim one item: write a line in `HANDOFF.md` under "In flight" (agent, date, item).
3. Prototype lemmas in `workspace/` with `formal-tools/check.sh workspace/Foo.lean`. Do arithmetic
   for resource counts in `workspace/*.py` before you prove anything.
4. Move proven pieces into `bench/ShorECDLP/Submission/Entrant/`, then run `build.sh`, `axioms.sh` and `boundary.sh`.
5. Run `score.sh` to get the official metrics, then `snapshot.sh <name> "<one-line note>"`.
6. Record: append to `LOG.md`; for a scored candidate, add a row to `SCOREBOARD.md`; for an experiment,
   write `work-notes/experiments/<date>-<slug>.md` (copy `TEMPLATE.md`); update `HANDOFF.md`.
7. Commit the lab (`git add -A && git commit`). Do not push and do not `yukon submit` unless the human asked.
   Codex sub-agents cannot commit, because their sandbox makes `.git` read-only. They leave changes on disk, and the orchestrator commits them.

## Hard constraints (from the contract)

- Only the axioms `propext`, `Classical.choice` and `Quot.sound` are allowed. Forbidden anywhere in Entrant:
  `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial`, `@[extern]`, `@[implemented_by]`,
  `@[csimp]`, `debug.skipKernelTC`, and `native_decide`-style shortcuts (check `benchmark.sh`'s FORBIDDEN list).
- Submission data must not depend on `Q`: a coefficient table, a straight-line program over
  X/H/CX/CCX/P/measure-reset (optional gates only via `whenBit`/`recordGate`), and a decoder layout.
- Organizer limits: gate slots ≤ 4·10^15, measurements ≤ 47,471,340,504, coefficient rows ≤ 983,040,
  candidate checks ≤ 56·(2^49+2).
- Cost model: CCX = 7 T, every `P(dir,k)` = 1 T, and qubits = distinct wires.

## Etiquette

- Small, verified steps. A compiling, scored snapshot beats an ambitious unproven plan.
- Write down dead ends with the reason; they are as valuable as wins.
- Long builds: run them in the background and log to `logs/`. Record wall times in notes so others can plan.
- Never delete another agent's snapshot or notes. Supersede them and say so.
