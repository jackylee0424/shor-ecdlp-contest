# Fast multiplier feasibility (Brief 20)

> **Brief 22 correction (2026-10-29): this feasibility verdict is superseded.**
> The count below charges one `A(L)` pass for erasing the canonical signed-add
> quotient, but addition and subtraction require different predicates selected
> by a live quantum sign.  That selection is not a Clifford terminal phase and
> is not covered by the 4-P unconditional-CCX lowering.  The direct exact
> phase-safe fallback (conditional add/compare/unadd plus overflow cleanup)
> projects only **856 × 8,419,666,672 = 7,207,234,671,232**, a
> **0.722413023%** cut versus leader `32b7d38`, below Brief 22's mandatory 2%
> gate.  See `work-notes/experiments/2026-10-29-fastmul-build.md` and
> `workspace/fastmul_build.py`.  The 24-lane carry construction itself remains
> valid; its checked literal count is 503 CCX, not the conservative 504 below.

## Verdict first

**Feasible at `w = 0`; not yet build-ready.**  The quotient-flag obstruction from
Brief 16 is removable without reconstructing the old accumulator.  Canonicalise
the signed modular add *before* doubling/halving, then erase its quotient from the
corrected result and the surviving addend.  For doubling modulo the odd secp256k1
prime, the quotient is exactly the corrected result's low bit, so its held flag is
cleared by one CNOT.

A conservative exact pass design fits the three 25-clean-lane sites: one lane owns
the quotient flag and 24 lanes run a chunked carry schedule.  Its best point is

```text
w = 0, 856 qubits
T = 10,989,894,224
score = 9,407,349,455,744
vs patch 10 = -4.551066%
vs leader 9,857,180,674,304 = -4.563488%
```

Every positive `w` in `0…64` has lower T but a worse score than `w=0`.  The patch
would not meet the lab's >10% submission policy.  Building the complete stack patch
is **XL**: the arithmetic identities and one-bit measurement semantics are checked,
but the chunked variable/constant passes, physical schedules, coherent composition,
resource theorems and six call-site wrappers do not yet exist as Lean circuits.
This note is therefore a feasibility/count result, not a certificate or achieved
Entrant score.

Reproduce:

```sh
python3 workspace/fastmul_feasibility.py
BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/FastMulAlgebra.lean
BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/FastMulFlag.lean
BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/MulClean.lean
```

## 1. Exact quotient-flag erasure

Let `0 ≤ z,y < p` and let `r` be the canonical result.

- Addition: if `t = [p ≤ z+y]`, then `r=z+y-tp` and **`t=[r<y]`**.
- Subtraction: if `t=[z<y]`, then `r=z-y+tp` and
  **`t=[p≤r+y]`**.
- Doubling: if `t=[p≤2z]`, then `r=2z-tp`.  Since `p` is odd,
  **`t = r mod 2`**.

`workspace/FastMulFlag.lean` proves these identities.  It also proves, directly
against `MeasurementUncompute.measureResetWithCorrection_coherent`, that a flag
which is a copy of a surviving output bit can be X-measured/reset and corrected by
a selected Pauli Z with zero T.  In the proposed double we do better: after the
correction, clear the quotient flag coherently with `CX r[0] flag`.

For the add/sub flag, X-measure it and run a phase-only full-width comparator.  The
comparator's carry ANDs are unconditional literal CCXs; only its final Z/CZ is
conditioned on the measurement record.  Thus patch 10 prices every nonlinear gate
at 5 T, while ordinary temporary-AND erasures cost zero T.  This avoids the bad
alternative of coherently reconstructing the entire pre-correction word and then
uncomputing it.

The other suggested routes are inferior or inapplicable:

- A single Gidney measured-AND with Clifford fix-up works only when the flag is a
  degree-two product of surviving bits.  The add/sub quotient is a 256-bit carry,
  so it needs the comparator phase oracle.  The double flag is the special copied-
  bit case proved in Lean.
- Keeping all flags coherent until a later inverse needs 255 flags per call, beyond
  `w≤64`.  Measuring them into receipts merely defers the same phase debt unless a
  later inverse is proved to regenerate every predicate in the same order.  No such
  cross-call invariant exists at the three post-EEA boundaries.
- Generic `recomputeZCorrection` is exact but computes and uncomputes the predicate.
  The phase-only carry pass below computes it once, pays a Clifford phase, and
  measurement-erases its carries.

## 2. The exact chunked pass

Write `A(P)` for one exact 256-bit carry/add/phase pass with `P` clean carry lanes.
The schedule is the donor's fewest-chunk rule, but the count is worst-case rather
than mean-weighted:

1. compute 256 carry ANDs, one CCX each;
2. keep one boundary carry between chunks;
3. measurement-erase ordinary carries for zero CCX;
4. for every non-final boundary receipt, run its exact chunk comparator as an
   unconditional phase oracle and charge one CCX per word lane in that chunk.

If the chunk lengths are `l₀,…,lₘ`, with the last chunk maximal, then

```text
A(P) = 256 + l₀ + … + lₘ₋₁ CCX.
```

Twenty-three lanes can cover at most 253 word positions.  Twenty-four is the first
feasible pool; its exact schedule and count are

```text
23,22,21,20,19,18,17,16,15,14,13,12,11,10,9,8,8
A(24) = 256 + 248 = 504 CCX.
```

One quotient flag plus those 24 carry lanes uses exactly the 25 clean lanes proved
at the tight sites.  No constant-|1⟩ lane is needed: public constant controls lower
to X/CX.  `workspace/fastmul_feasibility.py` constructs every schedule and rejects
an infeasible pool rather than extrapolating it.

For `L` total clean lanes, define:

```text
M(L) = 3*A(L-1) + A(L)       exact signed modular add/sub
D(L) = 2*A(L-1)              exact modular double
H(L) = A(L)                  exact modular halve
F(L) = 256*M(L) + 255*D(L)   forward call
I(L) = 256*M(L) + 255*H(L)   inverse call
```

`M` consists of the raw add, the near-`p` quotient toggle, the controlled `c`
correction, and (after flag reset releases its lane) the output/addend phase
comparator.  `D` computes `[z≥ceil(p/2)]`, rotates, adds controlled `c`, and clears
the flag from the output low bit.  `H` uses the input parity directly.  `F` and `I`
include all 255 recurring cells and the terminal signed modular add; nothing is
left at the donor's approximate 64/32-bit widths.

## 3. The three exceptional states and exact repairs

| Donor shortcut | Exact replacement | Worst-case cost | Extra wires |
|---|---|---:|---:|
| Drop the fold carry above lane 63/65 | Abandon the truncated fused table; use a full 256-bit chunked controlled-`c` pass | `A(L-1)` while the quotient flag is live | 0 beyond the proved `L`; one of the `L` lanes is the flag |
| Erase overflow from only the top 32 lanes | Measure the canonical add/sub quotient, then run the full output/addend phase comparator | `A(L)` CCX + 1 flag measurement; carry erasures are 0 CCX | 0; the measured flag rejoins the pool |
| Assume the post-fold high bit | Compute the exact doubling quotient `[z≥ceil(p/2)]`, add controlled `c`, then clear it from corrected bit 0 | `D(L)=2*A(L-1)` CCX | one flag already included in `L`; 0 net new wires |

At the three site widths with `w=0`, the exact primitives and calls are:

| Site | Clean `L` | `A(L-1)` | `A(L)` | `M(L)` | `D(L)` | `H(L)` | Forward call | Inverse call |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ordinary multiplier | 68 | 448 | 447 | 1,791 | 896 | 447 | **686,976** | **572,481** |
| square | 69 | 447 | 446 | 1,787 | 894 | 446 | **685,442** | **571,202** |
| post-EEA tight | 25 | 504 | 501 | 2,013 | 1,008 | 501 | **772,368** | **643,083** |

All counts are CCX before the patch-10 price.  The existing call is 1,110,533 CCX.
The proposed worst call is therefore the 25-lane forward call at 772,368 CCX; it
does not reach the 631,319-CCX break-even for a 901-qubit design, but it wins at the
unchanged 856-qubit width.

## 4. Call mix and exact total

The eight sites per corrected window are direction-sensitive:

| Lane class | Calls/window | Exact mix |
|---|---:|---|
| ordinary, 68 clean | 3 | 2 forward + 1 inverse |
| square, 69 clean | 2 | 1 forward + 1 inverse |
| post-EEA tight, 25 clean | 3 | 2 forward + 1 inverse |

At `w=0` this is **5,390,896 CCX/window**, versus
`8×1,110,533 = 8,884,264`.  Across 30 windows, at 5 T/CCX:

```text
old multiplier bucket = 1,332,639,600 T
new multiplier bucket =   808,634,400 T
Delta T               =  -524,005,200 T
```

Selected points from the complete `w=0…64` output follow.  Percentages are score
changes; negative is better.

| `w` | Qubits | T-model | ΔT | Q×T | vs patch 10 | vs leader |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 856 | 10,989,894,224 | −524,005,200 | **9,407,349,455,744** | **−4.551066%** | **−4.563488%** |
| 1 | 857 | 10,987,017,524 | −526,881,900 | 9,415,874,018,068 | −4.464574% | −4.477007% |
| 8 | 864 | 10,971,828,374 | −542,071,050 | 9,479,659,715,136 | −3.817391% | −3.829908% |
| 16 | 872 | 10,956,562,424 | −557,337,000 | 9,554,122,433,728 | −3.061877% | −3.074492% |
| 24 | 880 | 10,940,529,374 | −573,370,050 | 9,627,665,849,120 | −2.315690% | −2.328402% |
| 32 | 888 | 10,926,068,924 | −587,830,500 | 9,702,349,204,512 | −1.557937% | −1.570748% |
| 40 | 896 | 10,912,260,524 | −601,638,900 | 9,777,385,429,504 | −0.796604% | −0.809514% |
| 45 | 901 | 10,902,978,224 | −610,921,200 | 9,823,583,379,824 | −0.327870% | −0.340841% |
| 48 | 904 | 10,897,800,074 | −616,099,350 | 9,851,611,266,896 | −0.043493% | −0.056501% |
| 49 | 905 | 10,896,074,024 | −617,825,400 | 9,860,946,991,720 | +0.051229% | +0.038209% |
| 56 | 912 | 10,883,991,674 | −629,907,750 | 9,926,200,406,688 | +0.713304% | +0.700197% |
| 64 | 920 | 10,868,457,224 | −645,442,200 | 9,998,980,646,080 | +1.451747% | +1.438545% |

The calculator prints all 65 rows and, for each row, all six forward/inverse call
counts.  There is no discontinuity in this conservative construction: additional
lanes shorten phase-recomputed prefixes by only a few CCX per pass, far below the
score price of a qubit.  Hence `w=0` is the unique optimum.

## 5. What remains for a stack patch

The arithmetic blocker is resolved, but the implementation burden is substantial:

1. Build source-level chunked variable-add, constant-add and carry-phase passes with
   a proof that every held boundary receipt regenerates the same predicate.
2. Prove their coherent `MeasurementUncompute` contracts, exact CCX/measurement/
   support/slot counts, and record-cursor composition.  Ensure all comparator CCXs
   remain unconditional literals so patch 10 lowers them to 5 T.
3. Prove `M`, `D`, and `H` canonical on every secp256k1 input, including zero and
   the `p-c…p-1` boundary bands; then prove forward/inverse ladder composition.
4. Install width-specialized 68-, 69- and 25-lane schedules at the six Horner and
   two square call sites, preserving the `MulClean` boundary contracts.
5. Rebase onto `a72f4af` + stack patch 10, then run build, axioms, boundary and the
   official score.  No result in this note authorizes skipping that replay.

Estimated effort: arithmetic cell **L**, complete stack patch **XL**.  Because the
projected cut is only 4.55%, below current submission policy, this should not preempt
a >10% lever unless the policy or leader changes.
