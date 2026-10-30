# Exact divstep cell and replay audit

Brief 26, 2026-10-29. Checked Lean is in
`workspace/DivstepCellReplay.lean`; exact arithmetic and projections are in
`workspace/divstep_cell.py`.

## Verdict

**Stopped before the requested circuit milestone.** The arithmetic cell,
minimal transition state, branch-tag inverse, N-step replay, and a conservative
parametric width envelope are proved. There is still no `Straight` cell, no
basis-state theorem for emitted gates, no proved measurement phase repair, and
no circuit that converts the terminal scaled coefficient into the canonical
inverse. Consequently the CCX formulas and 256-bit Q/T rows below are
**extrapolated construction targets, not exact challenge receipts**.

This brief does establish two corrections to the old C7b screen:

1. `(δ,f,g)` is not enough for reverse replay. A forward branch tag, or a
   separately proved decision decoder from the cofactor state, is required.
   The proved fallback retains a four-way tag per active cell and Bennett-
   replays it.
2. The previously quoted `703 CCX/tick`, `W=340` profile priced neither a
   proved coefficient envelope nor clean replay. The envelope proved here is
   deliberately loose but scalable: value width `V=n+1`, coefficient width
   `C_t=t+2`, and delta width
   `H_t=1+ceil(log2(2t+2))`. At n=256 it is far wider and more expensive than
   that screen.

Submissions remain on hold. No Entrant or bench file was changed.

## 1. State choice and one-step refinement

The full scaled transition invariant in `DivstepMath` is

```text
2^ticks [f,g]^T = [[a,b],[c,d]] [f0,g0]^T.
```

Only the right column `(b,d)` is needed to recover `g0^-1 mod f0`, and that
column is closed under every branch. The cell state is therefore

```text
(delta2, f, g, b, d, ticks).
```

This removes the unused `(a,c)` row without weakening the inverse interface.
Lean theorem `project_mathStep` proves that projecting the full state to these
six fields commutes exactly with one `DivstepMath` step. The updates are:

| Branch | Condition | `(delta2,f,g)` output | `(b,d)` output |
|---|---|---|---|
| zero | `g=0` | unchanged | unchanged |
| even | `g` even, nonzero | `(δ+2,f,g/2)` | `(2b,d)` |
| swap | `g` odd, `δ>0` | `(2-δ,g,(g-f)/2)` | `(2d,d-b)` |
| add | `g` odd, `δ≤0` | `(δ+2,f,(g+f)/2)` | `(2b,d+b)` |

Odd `f` makes both odd-branch divisions exact. `step_f_odd` proves that this
precondition is preserved.

### Reverse rule

For post-state `(δ',f',g',b',d',t')`, the tagged inverse is:

```text
zero:  unchanged
even:  (δ'-2, f',       2g',      b'/2,       d',        t'-1)
swap:  (2-δ', f'-2g',   f',       b'/2-d',    b'/2,      t'-1)
add:   (δ'-2, f',       2g'-f',   b'/2,       d'-b'/2,   t'-1)
```

`unstep_step` proves this is a left inverse for every odd-`f` state.
`replay_trace` then proves structurally, for arbitrary N, that consuming the
chronological tag list in reverse returns the complete initial state. There is
no run cap and no sampled decoder in this theorem.

The abstract tag has four values, so two bits suffice mathematically. The
literal circuit sketch used for the count formula keeps three convenient raw
predicates (`active`, old parity `e`, and swap `sigma`), hence the conservative
support projection charges `3N` history wires. Compressing to `2N`, or
regenerating decisions from `(b,d)`, remains unproved.

## 2. Walk, cleanup, and measurement erasure

The exact safe cleanup rule is Bennett compute/copy/replay:

1. run N tagged cells;
2. compute the canonical inverse into a disjoint output register;
3. copy that computational-basis result;
4. apply the literal adjoint cells in reverse tag order.

Step 4 is proved at the arithmetic-state level. Step 2 is not built: the
terminal output of the proved recurrence is scaled,

```text
inverse = b * f * (2^ticks)^-1 mod f0,
```

and `ticks` is data-dependent because absorbing padding does not increment it.
The modular multiply/sign/variable-power decoder and its cleanup are therefore
an explicit missing cost. The projection below optimistically treats its copy
as Clifford and must not be used as a candidate bound.

### What may be measured away

The bench theorem `measureResetWithCorrection_coherent` permits an AND/carry
wire to be X-measured and reset only after a correction circuit supplies the
phase `(-1)^(outcome * old_bit)`. Applied to the proposed primitive skeleton,
the possible cuts are:

- the reverse half of the nonzero-test v-chain;
- carry-chain reverse sweeps in each controlled increment/negation;
- carry-chain reverse sweeps in the two mask/Cuccaro controlled additions.

The corresponding optimistic formula is

```text
C_mbu(V,C,H) = 6V + 6C + 2H - 6 CCX/cell.
```

It changes erased reverse-sweep CCX to zero T, with only Clifford selected
phase repair. No phase predicate/correction family for this cell is yet proved,
so this is labelled `MBU-unproved` everywhere.

Decision tags cannot simply be measured away. X-measuring a tag yields a
random phase transcript, not its Boolean branch value, while the adjoint needs
the actual branch. A cofactor decoder or retained quantum history is required.

## 3. Width envelope

Lean proves the following for every odd unsigned input, structurally rather
than by enumeration:

```text
|f_t|, |g_t| ≤ 2^n - 1
|delta2_t| ≤ 2*ticks_t + 1
|b_t|, |d_t| ≤ 2^ticks_t
ticks_t ≤ t.
```

Thus a safe public lane schedule is:

```text
V_t = n + 1
C_t = t + 2
H_t = 1 + ceil(log2(2*t + 2)).
```

The theorems are `step_valueBound`, `step_deltaBound`, `step_coeffBound`,
`walk_ticks_le`, `walk_envelopes`, and `unsigned_walk_envelopes`. This is a genuine fixed-width
envelope, but it is not the desired packed 340-lane envelope. At N=590 it
permits 592-bit signed coefficient words. Proving the much sharper product/
packing invariant needed for `W=340` remains the width milestone.

For small widths:

| n | All admissible pairs | Sharp steps | max `|f|,|g|` | max `|b|,|d|` | max `|delta2|` |
|---:|---:|---:|---:|---:|---:|
| 8 | 16,384 | 19 | 255 | 937 | 15 |
| 12 | 4,194,304 | 28 | 4,095 | 32,933 | 23 |

The n=8 and n=12 arithmetic/replay correctness follows from the all-integer
Lean theorems. Python additionally exhausts every admissible pair and checks
one-step inverse, full replay, gcd, and scaled inverse decoding. n=8 recomputes
by default; `python3 workspace/divstep_cell.py --exhaustive-n12` recomputes the
4,194,304-row n=12 receipt (about 2.5 minutes on this machine). This n=12
enumeration is calculator evidence, not a Lean `decide` claim.

## 4. Count formula

The conservative literal primitive plan uses a clean-v-chain nonzero test,
word Fredkins, controlled two's-complement negation, mask-plus-Cuccaro
controlled adds, a controlled coefficient shift, and delta update. Its target
count is

```text
C_raw(V,C,H) = 9V + 8C + 4H - 13 CCX/cell
walk_raw(N)   = N * C_raw
clean_raw(N)  = 2N * C_raw                 (compute + replay).
```

`cellCCX_closed` and `bennettCCX_closed` kernel-check the algebraic formula.
They do **not** count a constructed `Straight`; calling this an exact gate
receipt would be incorrect. The missing construction must prove each primitive
layout, basis action, scratch cleanup, support, measurements, record cursor,
gate slots, and the decoder discussed above.

Conservative standalone support used by the calculator is

```text
registers = H + 2V + 2C
output    = C
history   = 3N
scratch   = max(V+1, C+1, H-1)
support   = registers + output + history + scratch.
```

The challenge-Q screen replaces the leader's 580 EEA roles by this standalone
support. Sharing with the passenger and address bank is unproved.

## 5. n=256 extrapolation

All rows use `V=257`, `C=N+2`, the proved delta width, Bennett replay, 4-P
lowering, the old retained non-EEA T `1,175,358,444`, and 116 wrapper slots.
They omit the scaled-inverse decoder and are therefore sensitivity screens.

| N | Mode | V/C/H | CCX/cell | CCX/clean wrapper | support | Q screen | T screen | Q×T | vs leader |
|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 590 | raw | 257/592/12 | 7,084 | 8,359,120 | 4,665 | 4,941 | 5,053,990,124 | 24,971,765,202,684 | +243.978891% |
| 590 | MBU-unproved | 257/592/12 | 5,112 | 6,032,160 | 4,665 | 4,941 | 3,974,280,684 | 19,636,920,859,644 | +170.492943% |
| 724 | raw | 257/726/12 | 8,156 | 11,809,888 | 5,603 | 5,879 | 6,655,146,476 | 39,125,606,132,404 | +438.943984% |
| 724 | MBU-unproved | 257/726/12 | 5,916 | 8,566,368 | 5,603 | 5,879 | 5,150,153,196 | 30,277,750,639,284 | +317.067316% |
| 742 | raw | 257/744/12 | 8,300 | 12,317,200 | 5,729 | 6,005 | 6,890,539,244 | 41,377,688,160,220 | +469.965767% |
| 742 | MBU-unproved | 257/744/12 | 6,024 | 8,939,616 | 5,729 | 6,005 | 5,323,340,268 | 31,966,658,309,340 | +340.331534% |

The earlier conditional packed screen remains, for comparison only,
`952 × 1,367,811,724 = 1,302,156,761,248` at N=590. Nothing in this brief
proves its W=340 envelope, 703-CCX cell, replay, or decoder.

## 6. Next proof gate

Do not open an Entrant patch. The next reviewable unit is one literal n=8 cell:

1. allocate fixed word/history/scratch wires;
2. emit only permitted `Straight` gates;
3. prove its basis action refines `step` and its branch tag;
4. prove every scratch wire clean and constructor-derived CCX/support/record
   counts;
5. instantiate the generic measurement-uncompute theorem for one carry chain;
6. build and price the scaled-coefficient decoder.

Only after that should work return to the 340-lane packed invariant or a
cofactor-derived history decoder. The 590/724/742 termination theorem remains
Brief 25's independent obligation.
