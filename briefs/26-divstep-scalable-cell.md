# Brief 26 — scalable exact divstep cell (per-step circuit) at small widths, with a count formula to 256 bits

Read `AGENTS.md`, `docs/LEVERS.md` (C7b), **`docs/DIVSTEP-M1.md`** and **`docs/SMALLER-EEA.md`** (brief 23's BY screen: fixed ring width W = 340, Q = 952, ≈ 414,770
CCX/wrapper, projection 952 × 1,367,811,724; the unproved parts are the width envelope, the reverse/replay rule and the gate receipt), `workspace/DivstepMath.lean` (the recurrence and
matrix invariant; read it, don't edit), `workspace/smaller_eea.py`, `workspace/divstep_m1.py`, and `docs/ECDSAFAIL-855.md` (odinfree's Lilypad-G: uncontrolled add with
CNOT-derived sign, controlled swap, ~0.30M Toffoli/walk, public per-tick widths). Bench gate set and semantics: `ShorECDLP/Challenge/StraightLine.lean`, `Template.lean`
(X/H/CX/CCX/P/measure-reset; `whenBit`/`recordGate` only), and the measured-erasure lemmas in `Framework/Quantum/MeasurementUncompute.lean` (via `git -C ~/shorecdlp-m show 32b7d38:<path>`).
Submissions are on hold. Brief 25 is proving the iteration bound in parallel; assume a fixed horizon N (parameter, default 742).

## Goal

A **parametric** (in width n and step count N) exact circuit for the divstep walk that the 256-bit inverse will use, proved at small n:
1. **One divstep cell** on registers (δ, f, g) plus the transition-matrix state needed to recover the inverse (or the in-place "u, v, q, r" update, or another packed form; choose and justify):
   a constant-time conditional swap/negate, then g ← (g + (g₀-parity)·f)/2, then δ update. Fixed widths, no data-dependent control except via quantum controls.
   Prove its action on basis states equals one step of `DivstepMath`'s recurrence (refinement theorem), with clean scratch and an exact CCX count as a function of n.
2. **The walk:** N cells composed, the reverse/uncompute (replay) rule that returns all scratch and history to 0 while leaving f₀, g₀ and the inverse, and the measurement-based erasures
   where they cut T (CCX → 0 T with Clifford fix-up).
3. Prove correctness for **all inputs at n = 8 and n = 12** (kernel `decide` only where it is small; otherwise structural proofs), plus support/width and count theorems parametric in n.
4. **Width envelope:** the lane widths per step (fixed, as a function of the step index) with a proof, or a precise statement of what must be proved, that values stay within them.
   Extrapolate to n = 256, N ∈ {590, 724, 742}: qubits, CCX per walk/wrapper, T under 4-P lowering, and projected Q×T vs the leader 7,259,679,541,664.

## Where

Lean scratch `workspace/DivstepCell*.lean`, checked with `BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/DivstepCell<X>.lean` (`~/shorecdlp-m` at `32b7d38`; read-only otherwise).
Don't touch `~/shorecdlp` or `~/shorecdlp-c`. Don't edit `workspace/DivstepBound*.lean` (brief 25) or `DivstepMath.lean`; copy what you need.

## Output

`docs/DIVSTEP-CELL.md` (verdict first: proved vs extrapolated; the count formula; the width envelope status; the updated projection), Lean sources, `workspace/divstep_cell.py`,
a LOG line, and the LEVERS C7b row. No submissions or commits.
