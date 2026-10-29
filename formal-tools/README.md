# formal-tools

Bash scripts that run **inside WSL `gitzard-formal`**, where the Lean toolchain and the
benchmark checkout (`~/shorecdlp`) live. From Windows, prefix with the shim:
`formal-tools/w <tool> [args]` (Git Bash) or
`wsl -d gitzard-formal -- bash /mnt/c/code/shor-ecdlp-contest/formal-tools/<tool> [args]`.

| Tool | Purpose | Typical time |
|---|---|---|
| `check.sh FILE.lean` | Elaborate one file against the built library (fast inner loop; works on `workspace/` scratch) | seconds–minutes |
| `build.sh [Module ...]` | `lake build` (default `ShorECDLP.Submission.Entrant.Main`) | minutes |
| `axioms.sh [decl]` | `#print axioms` for the certificate (must be only propext / Classical.choice / Quot.sound) | minutes |
| `boundary.sh` | Verify nothing outside `Entrant/` differs (including untracked/ignored files) | instant |
| `score.sh [--yukon]` | Full official local benchmark → `scripts/score.json`, prints Q×T | long |
| `snapshot.sh NAME [note]` | Copy `Entrant/` (+ score.json) into `entrants/<date>-NAME/` | instant |
| `restore.sh DIR\|baseline` | Put a snapshot (or the pinned baseline) back into `Entrant/` | instant |
| `codex-agent.sh BRIEF.md` | Launch a Codex (`gpt-6.1-sol`) sub-agent on a brief | long |

Logs go to `logs/` (gitignored). All scripts source `env.sh`; override `BENCH`/`LAB` via env.
