# Brief 24 — Bernstein–Yang divsteps, milestone 1: kernel-checked 590-tick bound + exact n = 8 circuit

Read `AGENTS.md`, `docs/LEVERS.md` (C7b), **`docs/SMALLER-EEA.md`** (brief 23: BY590 conditional projection 952 × 1,367,811,724 = 1.302e12, about −82 % vs the leader;
the 340-lane width, the reverse/replay rule and the gate receipt are the unproved parts), `workspace/smaller_eea.py`, and `docs/ECDSAFAIL-855.md` (Lilypad-G lineage).
Primary source: Bernstein & Yang, "Fast constant-time gcd computation and modular inversion" (safegcd), https://gcd.cr.yp.to/safegcd-20190413.pdf, and its
later bound refinements. Submissions are on hold; this is research toward a future stack patch.

## Scope (milestone 1 only)

**Part A — termination certificate (pure Lean, kernel-checkable, no native_decide/bv_decide).**
Formalize the selected half-delta divstep recurrence (δ, f, g) exactly as the circuit will compute it. Prove that for every odd modulus f₀ = p (secp256k1's p, or
for all odd f₀ < 2^256) and every g₀ < f₀, after **590** iterations (or the smallest bound you can certify; state it) g = 0 and f = ±gcd = ±1. Also prove the transition-matrix
product yields g₀⁻¹ mod p. Prefer a proof that scales: an analytic potential-function/convex-hull argument, or a certificate checkable by kernel `decide` on small
structured objects (as in safegcd's "hddivsteps" bound proofs). It must not enumerate inputs. If 590 is out of reach, certify a larger bound (for example 724/741) and report its
cost impact with `workspace/smaller_eea.py`.

**Part B — exact small circuit.** Write a `Straight`/Adaptive builder for the full forward divstep walk at n = 8 (parametric in n where cheap) over the bench gate set
(X/H/CX/CCX/P/measure-reset, `whenBit`/`recordGate` only). It must have fixed widths and constant-time conditional swap/negate/halve, and keep the transition matrix
(or its packed equivalent) needed to recover the inverse. Then write its reverse/uncompute. Prove functional correctness for all 8-bit inputs (kernel `decide` is fine at n = 8 if
it is small), clean scratch, exact CCX count and support. Extrapolate the count formula to n = 256 and compare it with brief 23's 414,770 CCX/wrapper screen and the 340-lane envelope.

## Where

Lean scratch in the lab (`workspace/Divstep*.lean`), checked with `BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh` (the bench copy `~/shorecdlp-c` at `32b7d38`; read-only otherwise).
Don't touch `~/shorecdlp` or `~/shorecdlp-m`.

## Output

`docs/DIVSTEP-M1.md` (verdict first: the bound certified, its proof method, the n = 8 circuit results, the extrapolated 256-bit cost and the updated projection vs the leader 7,259,679,541,664),
Lean sources, `workspace/divstep_m1.py`, a LOG line, and a LEVERS C7b update. State plainly what is proved and what is extrapolated. No submissions or commits.
