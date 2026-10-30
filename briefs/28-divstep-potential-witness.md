# Brief 28 — construct the `Has256TrianglePotential` witness (closes the kernel-checked 742-step bound)

Read `AGENTS.md`, **`docs/DIVSTEP-BOUND.md`** and **`workspace/DivstepBound.lean`** (brief 25: kernel-checked
`halfDelta_terminates_742_of_certificate (hcert : Has256TrianglePotential)`, plus gcd preservation and `terminal_inverse_exists`; the only missing piece is a concrete
finite rational polyhedral potential for the 256-bit initial triangle that dominates |g| and contracts by 25/32 on every nonterminal half-delta step).
Literature: Bernstein–Yang safegcd §11–12 (https://gcd.cr.yp.to/safegcd-20190413.pdf) and sipa's safegcd-bounds (https://github.com/sipa/safegcd-bounds), whose Coq convex-hull
computation is the template. Its `vm_cast_no_check` shortcut is NOT admissible here; we need kernel-checkable data. Submissions are on hold.

## Goal

1. Compute the witness outside Lean (`workspace/divstep_hull.py`, exact rationals/integers; reproducible): the polyhedra/vertex sets and the contraction inequalities, at whatever
   granularity the certificate definition requires. Minimize its size (vertex count, coefficient bit sizes). If 25/32 contraction or the 742 horizon can't be met with a
   compact witness, report the best (contraction, horizon) pair you can certify.
2. Emit it as Lean data (`workspace/DivstepHull*.lean`, generated) and prove `Has256TrianglePotential` (or the adjusted variant) with **kernel-friendly** steps: `norm_num`/`decide` on
   small rational facts, structured as many small lemmas. No native_decide/bv_decide/ofReduceBool. Keep every file within leanchecker's recursion limits; measure the check time and memory.
3. Conclude the unconditional theorem `halfDelta_terminates_742` (or `_N` for the certified N) with axioms exactly propext/Classical.choice/Quot.sound.

## Where

Lean via `BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/DivstepHull<X>.lean` (`~/shorecdlp-c` at `32b7d38`, read-only otherwise). Copy, don't edit, `DivstepBound.lean`
if you need changes (put them in `DivstepBound2.lean`). Don't touch `~/shorecdlp-m` (brief 27) or `~/shorecdlp`.

## Output

`docs/DIVSTEP-BOUND.md` (append "Witness" section: result, N, size, check time), generator + generated Lean, a LOG line, and LEVERS C7b. No submissions or commits.
