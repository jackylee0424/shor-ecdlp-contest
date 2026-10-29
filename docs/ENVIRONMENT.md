# Environment

## Machines and paths

- Host: Windows 11 (`C:\code\shor-ecdlp-contest` = this lab, a git repo).
- Lean runs in WSL2 distro **`gitzard-formal`** (user `gitzard`, 20 cores, 54 GB RAM).
  - elan is at `/opt/gitzard/elan` (on `PATH` via login shell); the bench pins `leanprover/lean4:v4.28.0`.
  - The bench checkout is `/home/gitzard/shorecdlp`, cloned by `yukon clone a721dbcb-4a80-4074-853c-53534959dcb8`
    from `github.com/Layr-Labs/shor-ecdlp-lean` (branch `master`). Keep it on the Linux filesystem: Lean I/O
    over `/mnt/c` is slow.
  - The lab is visible from WSL as `/mnt/c/code/shor-ecdlp-contest`.
- Running something in WSL from Windows: `wsl -d gitzard-formal -- bash -lc '<cmd>'`
  (PowerShell mangles nested quotes, so put complex commands in a script file instead).

## Yukon CLI (benchmark platform)

Installed in WSL at `~/.local/bin/yukon` and already logged in. Run it from the bench:

```bash
cd ~/shorecdlp
yukon setup --track lean      # one-time: toolchain, Mathlib cache, trusted oleans
yukon run --track lean        # local verifier: leanchecker replay + judge -> scripts/score.json
yukon submit --track lean --dependencies-file dependencies.json   # ONLY when the human says so
```

Yukon **trace collection is on**: yukon commands upload the calling agent's transcript. Disable it with
`yukon trace off`. `formal-tools/score.sh` runs `./benchmark.sh` directly, without going through yukon.

## Codex sub-agents

- A Linux Codex CLI (`0.162.1`, from the official npm `@openai/codex@0.162.1-linux-x64`) is installed at
  `~/.local/opt/codex`, linked as `~/.local/bin/codex`.
- `CODEX_HOME=~/.codex-wsl`: `config.toml` (model `gpt-6.1-sol`, `sandbox_mode = workspace-write`,
  `approval_policy = never`, network on) and `auth.json`, which is a symlink to the Windows `~/.codex/auth.json`.
- Launch with `formal-tools/codex-agent.sh briefs/<brief>.md`. Writable roots are the lab plus the bench.
- Windows-side Codex cannot be used here: its Windows sandbox fails to spawn processes
  ("setup refresh had errors"), and unsandboxed mode is not permitted.

## Build facts (fill in as measured)

| Action | Wall time | Notes |
|---|---|---|
| `yukon setup --track lean` (cold) | ~40 min | 3,514 jobs, 20 cores |
| `check.sh workspace/Smoke.lean` | 3s | after Entrant built |
| `score.sh --yukon` (warm, baseline) | 1m45s | includes Entrant rebuild + leanchecker replay |
