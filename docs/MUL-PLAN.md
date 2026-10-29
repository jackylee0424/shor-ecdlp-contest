# C8 exact fast multiplier: feasibility result

## Single-trial re-audit (`c13a293`, Brief 16)

The dadon single-trial base has 30 corrected windows, not the older six-round schedule.
The checked lane inventory is unchanged: five replacement sites have 68–69 clean lanes
and three post-forward-EEA sites have only 25. There are eight calls/window and each call
is `1,110,533 CCX`, with 255 recurring 4,344-CCX add/double cells plus a terminal
2,813-CCX add.

At 855 qubits the exact 3% gate is

```text
5 * spaciousCellCCX + 3 * tightCellCCX < 26144.023001.
```

The ecdsa.fail donor emits about 540 CCX/bit at a 76-lane pool, but that figure retains
three inadmissible exceptional-state shortcuts: a 64-lane fold, a 32-lane overflow erase,
and an assumed post-fold high bit. The exact fused integer reduction has correction
`d+B-q*p`, `B=2*(-1)^s*k*c+h*(c-1)`, and `q∈{-1,0,1}`. Dirty MCX can compute the narrow
boundary predicate while restoring donors, but the quotient flag still needs an exact
phase-safe erase after the word correction. The current library offers only a full word
reconstruction/compare for that step; no continuation-aware narrow erasure theorem exists.

Consequently Brief 16 did not pass the exact-count gate. The achieved patch cut is 0%; no
Entrant or stack patch was created. Reproduction and conditional sensitivity calculations:
`workspace/dirtyfold_feasibility.py`; algebra: `workspace/FastMulAlgebra.lean`; full record:
`work-notes/experiments/2026-10-29-dirtyfold-mul.md`.

Brief 13, 2026-10-29. **Stopped at the required feasibility gate.** The frontier does not
prove the roughly 70 clean lanes required by the proposed modp_ft-style cell at every call
site. Three Horner calls have only **25** clean lanes outside their 256-bit destination.
No bench file was changed and no multiplier score is claimed.

Reproduce the checked clean-lane facts and the integer projections with:

```sh
BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/MulClean.lean
python3 workspace/mul_feasibility.py
```

The Lean check imports the protected frontier at `93051d2`; it uses no new axiom and no
native decision shortcut.

## Call-site inventory

Ranges are inclusive. “Clean” means proved zero for every supported input at that exact
boundary, not observed zero on samples. The destination itself is excluded even when it is
clean on entry because the multiplier must write it.

| Call | Schedule position | Destination | Clean lanes available outside destination | Count | Proof anchor |
|---|---|---|---|---:|---|
| division multiply-to-work | forward EEA → `fig15MultiplyToWork` | 7–262 | 4–6, 558–579 | **25** | `secp256k1EEAOutputIdealState_correct` |
| division recompute | reverse EEA → `fig15MultiplyToData` | 580–835 | 0–6, 519–579 | 68 | `fig15DivisionRestoredState_eq`, original `Secp256k1InPlaceInputValid` |
| division unrecompute | correction → `fig15MultiplyToDataInverse` | 580–835 | 0–6, 519–579 | 68 | `fig15DataProductState_correct` frame |
| multiplication multiply-to-work | entry → `fig15MultiplyToWork` | 7–262 | 0–6, 519–579 | 68 | `Secp256k1InPlaceInputValid` |
| multiplication recompute | forward EEA in data bank → `fig15MultiplyToData` | 580–835 | 4–6, 558–579 | **25** | relabel of `secp256k1EEAOutputIdealState_correct` |
| multiplication unrecompute | correction → `fig15MultiplyToDataInverse` | 580–835 | 4–6, 558–579 | **25** | preceding output contract plus `fig15DataProductState_correct` frame |
| square compute | `squareLoop` before subtraction | 7–262 | 0–6, 519–579, 837 | 69 | `Secp256k1ZeroAllowedInputValid` |
| square uncompute | subtraction → `squareLoopInverse` | 7–262 | 0–6, 519–579, 837 | 69 | `squareSubtract_correct` frame |

Why the post-EEA set collapses to 25 is structural. The public EEA output theorem proves
`Clean (4..262)`, label 559 false, and `IndexedStepReady`, whose shared scratch is label 558
and 560–579. The Horner destination consumes 7–262. Thus only 4–6 and 558–579 remain.
Relabeling the EEA into the data bank moves 7–262 to 580–835 but leaves the same 25-lane
remainder.

Labels 836 and 838 carry live point/control state. Label 837 is the zero-input flag inside
the two Figure-15 wrappers and may be true, so it is unavailable to all six Horner calls.
It is clean only at the outer square call. Labels 855–870 hold the coherent address bank.
The gap 839–854 is outside the present support; touching it increases qubits rather than
providing a free loan.

## Exact algorithm that was being tested

The intended exact cell follows the algebra of the cited modp_ft lineage but not its rate
assumptions:

1. Recode an n-bit multiplier as
   `2^(n-1) + Σ(k<n-1) (2 a[k+1]-1) 2^k - (1-a[0])`. Each digit is therefore an
   unconditional `+y` or `-y`; the sign is Clifford complement conjugation.
2. Fuse each signed add with its following double (and use the inverse halve form on the
   reverse path). For `p = 2^256-c`, `c=2^32+977`, combine the raw carry and shift bit into
   `δ∈{-2,-1,0,1}` and add `δc` once over the low 66-lane fold window.
3. Unlike the donor, propagate the fold carry through all remaining lanes, erase the raw
   overflow with a full 256-lane comparison, and use the exact halve form (or a full boundary
   test) rather than identifying the high bit probabilistically.
4. Measurement-uncompute every logical-AND carry and return all scratch clean. The square
   uses one clean copy of the digit sign so that the sign control never aliases the addend.

The donor's direct fused table needs 74 pool lanes plus its overflow flag; the proposed
chunked version was gated on approximately 70 and the donor already shows a cost cliff below
47. A 25-lane pool is not a small shortfall: it cannot instantiate either layout. Replacing
the missing lanes with dirty borrowers would be a different cell requiring restoration,
coherence and a new exact count; no such theorem exists in the frontier.

Because feasibility failed, there is **no exact worst-case count for a new call** and no
functional-correctness claim. Assigning the estimated 600–1,000 CCX/bit to a nonexistent
circuit would violate the brief's exact-count requirement. The exact current costs and
conditional budget below delimit what a future dirty-borrowed design must prove.

## Exact resource bounds and projections

The current call costs are machine-checked:

- one Horner forward or inverse call: **1,110,533 CCX = 7,773,731 T**;
- six calls/window: **46,642,386 T**;
- two square ladders/window: **15,547,462 T**;
- the square's retained modular subtraction: **2,813 CCX = 19,691 T**;
- all eight replaceable calls over 28 windows and six rounds: **10,447,894,464 T**.

For a hypothetical exact replacement with `c_bit` CCX/bit and `F` fixed CCX/call, the exact
frontier projection is

```text
T = 75,791,941,566 + 2,408,448*c_bit + 9,408*F
score = 855*T.
```

This is a budget equation, not an achieved circuit count.

| Conditional cell budget | T-model | Q×T | Cut vs `ff1bf8d` | Margin to strict policy bar |
|---:|---:|---:|---:|---:|
| 600 CCX/bit, F=0 | 77,237,010,366 | 66,037,643,862,930 | 10.439288939% | passes by 323,909,962,155 |
| 757 CCX/bit, F=0 | 77,615,136,702 | 66,360,941,880,210 | 10.000829924% | passes by 611,944,875 |
| 758 CCX/bit, F=0 | 77,617,545,150 | 66,363,001,103,250 | 9.998037191% | misses by 1,447,278,165 |
| 800 CCX/bit, F=0 | 77,718,699,966 | 66,449,488,470,930 | 9.880742423% | misses by 87,934,645,845 |
| 1,000 CCX/bit, F=0 | 78,200,389,566 | 66,861,333,078,930 | 9.322195906% | misses by 499,779,253,845 |

Thus the more precise target is at most **757 CCX/bit with at most 76 fixed CCX/call**. The
headline 600–1,000 interval is too broad for the human submission policy.

Adding the 45 missing lanes to reach 70 would make 900 qubits. Even if all eight calls then
cost zero T, the score would be **68,212,747,409,400**, only a **7.489398409%** cut and still
1,851,193,584,315 above the policy bar. Extra qubits cannot rescue this implementation route.

For stacking context, a hypothetical 758-CCX/bit cell misses alone by 1,447,278,165 score;
Brief 12's C3 or C4 saves 13,031,020,800 or 26,062,041,600 score and would clear that case.
At 800 CCX/bit, C3/C4 still leave misses of 74,903,625,045 / 61,872,604,245. The achieved
multiplier saving in this brief is **zero**, so there is presently nothing to stack.

## What would reopen C8

C8 remains viable only after one of these new prerequisites is proved:

- a ≤25-clean-lane exact signed fold with a kernel-checked worst-case cost low enough to meet
  the 757-CCX/bit envelope;
- a dirty-borrowed fold/compare whose donors are restored at all three post-EEA sites;
- or an EEA output/layout change that proves at least 45 more lanes clean without increasing
  complete support.

Each option changes the algorithm or the EEA boundary. None is the requested direct
modp_ft-style transplant, so Brief 13 stops before Entrant integration.
