# Brief 02 — bench codebase map and resource breakdown of the shipped entrant

Read `AGENTS.md` and `docs/CHALLENGE.md` (in the lab, your cwd) first. The bench is `~/shorecdlp` (WSL).

## Goal

1. Fill `docs/CODEBASE-MAP.md`: one line per important module under `ShorECDLP/{Challenge,Framework,Math,
   Submission/Naive,Submission/2607_13816,Submission/Entrant}`. Give the path, what it provides, and the key
   defs/theorems an entrant would import. Read the bench docs (`docs/PLAN.md` headings, `docs/STREAMING_*.md`,
   `docs/NAIVE_*.md`, `Submission/2607_13816/INTEGRATION.md`, `REFERENCE.md`).
2. Resource breakdown of the shipped Entrant (206,642 qubits, 355,060,161,799,520 T-model, 530 measurements):
   attribute qubits and T to subroutines (adder, modular reduction, multiplication, Fermat inversion,
   point add/double, controlled versions, QFT, number of scalar-multiplication steps). Use the definitions
   and resource lemmas in the source. Write `workspace/baseline_breakdown.py`, which reproduces both totals
   exactly from per-subroutine formulas, and summarize it in `docs/BASELINE-BREAKDOWN.md`.
3. 2607_13816 status: what is proved, what is missing, and a rough size of the remaining work (from
   `INTEGRATION.md`, `docs/STREAMING_*.md` and the code), all in `docs/BASELINE-BREAKDOWN.md` under its own heading.

Do not modify the bench. If you need to elaborate Lean to confirm a count, put scratch in `workspace/` and
use `formal-tools/check.sh` (the bench may still be building: if `lake` reports missing oleans, rely on reading the source).

## Output

`docs/CODEBASE-MAP.md`, `docs/BASELINE-BREAKDOWN.md`, `workspace/baseline_breakdown.py`, one line in
`work-notes/LOG.md`. Done when the Python script prints exactly 206642 and 355060161799520 (or explains,
with cited lemmas, why the declared bound is looser than the true count).
