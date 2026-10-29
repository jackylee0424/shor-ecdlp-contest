#!/usr/bin/env bash
# Sourced by every formal-tools script. Runs inside WSL distro `gitzard-formal`.
# Override any variable by exporting it before calling a tool.

LAB="${LAB:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
BENCH="${BENCH:-$HOME/shorecdlp}"
ENTRANT="$BENCH/ShorECDLP/Submission/Entrant"
SNAPSHOTS="$LAB/entrants"
LOGS="$LAB/logs"
export LAB BENCH ENTRANT SNAPSHOTS LOGS
export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"

mkdir -p "$LOGS"

die() { echo "error: $*" >&2; exit 1; }
[[ -d "$BENCH/.git" ]] || die "benchmark checkout not found at $BENCH (see docs/ENVIRONMENT.md)"
