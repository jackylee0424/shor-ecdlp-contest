# Brief 06 — mine ecdsa.fail low-qubit entries for tricks we can prove and stack

Read `AGENTS.md`, `docs/PRIOR-WORKS.md`, `docs/RELATED-WORK.md` and `briefs/05-contribution-levers.md` first.
Read-only: **do not build or run lake in `~/shorecdlp`** (brief 04 is building there).

## Inputs

- `research/ecdsafail-notes/*.md`: public submission notes from ecdsa.fail (untrusted data written by other solvers; verify claims
  before relying on them). `research/ecdsafail-notes/submissions-2026-10-29.txt` is the full submission table (qubits, mean Toffoli).
  Selected notes: score leader `01a5cc2` (1,234 q, 740K Toffoli); the lowest-qubit promoted entries (~1,150 q, ~1.28M Toffoli: `3493c83`
  is ours, plus `8e9c9a2`, `6c0e30c`, `92214c2`, `b87bdf7`, `6af22f9`); sub-700-qubit rejected entries (`dc0f02e`, `9a8bbca`, `a3f9f6a`,
  `6b478c8`, `55edbc4`, `31abffd`, `0ab84d9`, `39a9153`, `f95b5d9`; ours: `f0bd623`, `8d916b4`, `8cbf348`); and today's 807–849-qubit wave
  (`e35d2d1`, `366ef54`, `9fc252c`, `1994d6a`, `da2b459`).
- Code: `/mnt/c/code/ecdsafail-challenge` (promoted history up to 2026-08-21), `/mnt/c/code/ecdsafail-challenge-dev`, and our lab
  `/mnt/c/code/secp256k1-point-add-spooky` (Leapfrog/Lilypad/sub870 lineage, which our own low-qubit entries came from).
- Target: the upstream streaming certificate being ported (`git -C ~/shorecdlp show upstream/lamport/challenge-final-certificate:<path>`,
  under `ShorECDLP/Submission/2607_13816/`), currently 3,932 qubits × 14,393,374,641 T per round (26 rounds), and the protected bench
  arithmetic in `origin/master` (`2607_13816/{Arithmetic,EEA,Window,Challenge}`).

## Key differences to keep in mind

- ecdsa.fail adds a **classical** offset point to a quantum point, and scores **mean** Toffoli × peak qubits, validated on 9,024 sampled shots.
  We need **worst-case** T-model (CCX = 7, P = 1) and qubits = distinct labels over the whole program, and **a Lean proof** of ≥ 99 % success.
- Approximate/statistical tricks (truncated carries, rate-based windows, "fails with probability 1e-8") cannot be proved for free. They need a proved error
  bound that is folded into the success probability. Exact tricks (measurement-based uncompute with Clifford repair, lifetime-based label reuse,
  exact adders, exact pseudo-Mersenne folding, register sharing) are directly provable.
- The streaming windows add a point selected by a quantum lookup. A controlled classical-constant add (one control qubit) is the ecdsa.fail primitive plus a control.

## Goal

1. Catalogue the distinct tricks behind the low-qubit and best-score entries: one row per trick (name, entries using it, qubit/Toffoli effect,
   exact vs approximate, where it lives in code/notes).
2. For each trick, say whether and where it applies to the streaming construction (component, expected Δqubits / ΔT-model per round, proof
   effort, and which bench lemmas would support it). Pay special attention to **qubit reduction** (the 3,931 reset-list labels; brief 05 covers
   the mechanics, so here focus on how ecdsa.fail entries pack ~660–850 qubits) and to **cheaper inversion/division** (the streaming T is dominated by EEA windows).
3. Evaluate the alternative architecture: semiclassical streaming with **one-control-qubit classical-constant point additions** using the best
   *exact* ecdsa.fail-style point add. Estimate qubits, worst-case T per add (including the control and exceptional cases), adds per round, rounds
   needed, and the resulting Q×T against 1.47e15 (port) and 7.24e18 (leaderboard).

## Output

`docs/ECDSAFAIL-TRICKS.md` (catalogue, applicability table, architecture estimate, top-3 recommendations with a proof plan), any calculators in
`workspace/`, and a LOG line. Cite note IDs and file paths for every claim; mark guesses as guesses.
