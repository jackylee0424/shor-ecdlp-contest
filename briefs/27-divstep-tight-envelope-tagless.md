# Brief 27 — divstep: tight width envelope + tag-free replay (the two pieces that decide whether the route wins)

Read `AGENTS.md`, `docs/LEVERS.md` (C7b), **`docs/DIVSTEP-CELL.md`** (brief 26: proved minimal state (δ, f, g, b, d, ticks), tagged one-step inverse, N-step Bennett replay,
loose envelopes V = n+1, C_t = t+2, H_t = 1+⌈log₂(2t+2)⌉. With those, 256-bit at N = 590 is 4,941 × 5.05e9 ≈ 2.50e13, about 2.4× worse than the leader 7,259,679,541,664.
The −82 % screen assumed W ≈ 340 lanes and no tags), `docs/SMALLER-EEA.md`, `docs/DIVSTEP-BOUND.md`, `workspace/DivstepCellReplay.lean`, `workspace/DivstepMath.lean`,
`workspace/divstep_cell.py`. Literature: Bernstein–Yang safegcd (https://gcd.cr.yp.to/safegcd-20190413.pdf; the bounds on transition-matrix entries,
|u|,|v|,|q|,|r| ≤ 2^t), libsecp256k1's `doc/safegcd_implementation.md` (batched 62-step matrices, coefficient ranges), and odinfree's Lilypad-G packing (`docs/ECDSAFAIL-855.md`).
Submissions are on hold.

## Goals

1. **Tight coefficient envelope.** The proved `C_t = t+2` grows without bound. Prove the real constraint: the *reduced* coefficients needed for the inverse can be kept mod f₀
   (or in a fixed n+O(1)-bit window) by folding/modular halving each step, or by batching (libsecp-style matrices on 62-step blocks, then applying the block to the modular
   (b, d)). Give the exact lane count per register for n = 256 and its proof obligations. Target the screen's ≈ 340 lanes for f/g plus a modular-width (b, d).
2. **Tag-free replay.** Prove a decision decoder: from the post-step state (δ', f', g', and whatever packed cofactor state you keep), recover the branch taken (swap/negate or not, and
   the parity bit), so the inverse step needs no stored tag. Known handles: the sign of δ', the parity relation of g', and f' unchanged versus swapped. If impossible in
   general, give the minimal extra state (bits per step, or a block-level checkpoint) and its qubit cost.
3. **Re-price** with what you prove: qubits, CCX per walk/wrapper, T under 4-P lowering, and Q×T vs 7,259,679,541,664 at N = 742/724/590. Price each step as exact (CCX = 4 under the leader's lowering; measured erasures 0).
4. Prove (1)–(2) at n = 8 and n = 12 for all inputs, plus parametric statements where feasible.

## Where

Lean scratch `workspace/DivstepTight*.lean`, checked with `BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh` (`~/shorecdlp-m` at `32b7d38`, read-only otherwise). Copy, don't edit, existing
Divstep files. Don't touch `~/shorecdlp-c` (brief 28) or `~/shorecdlp`.

## Output

`docs/DIVSTEP-TIGHT.md` (verdict first: does the proved design beat the leader, and by how much?), Lean, `workspace/divstep_tight.py`, a LOG line, and LEVERS C7b. No submissions or commits.
