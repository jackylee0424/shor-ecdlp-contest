# Brief 25 — kernel-checkable Lean proof of the Bernstein–Yang divstep iteration bound (target: 742 steps at 256 bits)

Read `AGENTS.md`, `docs/LEVERS.md` (C7b), **`docs/DIVSTEP-M1.md`** (brief 24: what is already kernel-checked in `workspace/DivstepMath.lean`, namely the half-delta recurrence,
odd-f preservation, the scaled transition-matrix invariant and the conditional Bezout row; and why the safegcd Coq 590/724 receipts are inadmissible: `vm_cast_no_check`).
Primary source: Bernstein & Yang, "Fast constant-time gcd computation and modular inversion", https://gcd.cr.yp.to/safegcd-20190413.pdf, especially the divstep
iteration bound (d ≤ ⌊(49d + 80)/17⌋ for d ≥ 46, about 742 at d = 256; and the 2-adic / transition-matrix-norm argument with its finite computation). Submissions are on hold.

## Goal

A Lean proof, checked by the kernel with only propext/Classical.choice/Quot.sound (no `native_decide`, `bv_decide`, `Lean.ofReduceBool`, or `decide` on huge objects), that:
1. for every odd f₀ and every g₀ with 0 ≤ g₀ < 2^256 (or < f₀ ≤ 2^256), the **chosen** divstep recurrence (the same one formalized in `DivstepMath.lean`; state precisely whether it is
   the classic δ or the half-delta variant, and adapt the bound accordingly) reaches g = 0 within **N** steps, with N ≤ 742 (or the best certified N; report it);
2. at that point f = ±gcd(f₀, g₀), and with the existing matrix invariant this gives g₀⁻¹ mod f₀ when the gcd is 1 (in particular for f₀ = p of secp256k1).

## Method guidance

- Follow the paper's proof structure: the norm/potential argument over transition matrices, with the finite verification split into small, kernel-friendly lemmas
  (an explicit finite set of matrix products or a recursive bound table checked with `decide` on *small* rational or integer data, or `norm_num`).
- If the paper's finite computation is too large for the kernel, find a decomposition: induction on bit-length with a per-block bound, or certified interval arithmetic with
  rational endpoints. Measure elaboration time and memory, and keep every file under the leanchecker recursion limits (the bench judge replays with leanchecker).
- A weaker but proved bound is acceptable (for example ≤ 800); report the score impact using `workspace/smaller_eea.py` / `workspace/divstep_m1.py`.

## Where

Lean scratch in the lab: `workspace/DivstepBound*.lean` (import `workspace/DivstepMath.lean` content as needed; copy, don't edit, if another brief owns it).
Check with `BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/DivstepBound<X>.lean`. Don't touch `~/shorecdlp` or `~/shorecdlp-m` (brief 26 uses `~/shorecdlp-m`).
Don't edit `workspace/DivstepCell*.lean` (brief 26).

## Output

`docs/DIVSTEP-BOUND.md` (verdict first: the theorem proved, N, axioms, check time; or the exact blocking lemma), Lean sources, a LOG line, and the LEVERS C7b row. No submissions or commits.
