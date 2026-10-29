# Fewer windows in the single-trial design

## Verdict

**No certifiable combination in this brief clears the −10% submission bar.** The only arithmetic
combination that does clear it is `wrappedShift` at 263/203 bits plus row-optimal packing: 29
signed additions instead of 33, projected at **855 × 14,853,077,112 = 12,699,380,930,760**
(**−12.120916%**) with the leader's existing physical lookup, or conditionally
**855 × 14,832,203,896 = 12,681,534,331,080** (**−12.244414%**) with width-specialized lookup
trees. It is not a submission candidate: a single `wrappedShift` trial has a nearest-bin bottleneck
on the right axis. For the uniform requirement, already `d = 1` has success near
**0.7736950099**, and a simple upper decomposition keeps it below about 0.779, nowhere near 0.99.

The best plausible valid precision improvement is `nearestPair` at **262/262**. An averaged
rounding-window proof should give a uniform lower bound near **0.9936677**, but it saves only 524
Fourier-phase T gates and no addition window. Combined with width-specialized 15-bit lookup trees,
the exact projection is **855 × 16,871,901,094 = 14,425,475,435,370** (**−0.176428%**). This is
well above the submission bar **13,005,873,923,211**.

All integer resource and candidate-budget results below are exact and reproduced by
`python3 workspace/fewer_windows.py`. Mass decimals are large-order sinc diagnostics, not
machine-checked finite-order values. No bench file was changed and no score was run.

## Ranked result

| Rank | Combination | Status | Signed additions | Rows | T-model | Q×T | vs leader | Effort |
|---:|---|---|---:|---:|---:|---:|---:|---|
| 1 | `nearestPair` 262/262 + specialized 15/16-bit trees | **plausibly valid; not proved here** | 33 | 819,200 | 16,871,901,094 | 14,425,475,435,370 | −0.176428% | L |
| 2 | `nearestPair` 263/263 + specialized 15/16-bit trees | Semantics unchanged; tree specialization unproved | 33 | 851,968 | 16,874,883,506 | 14,428,025,397,630 | −0.158783% | M/L |
| 3 | `nearestPair` 262/262, existing physical tree | Plausibly valid; no window saved | 33 | 819,200 | 16,901,719,974 | 14,450,970,577,770 | −0.000003% | L |
| 4 | `wrappedShift` 263/203 + specialized trees | **invalid success** | 29 | 786,432 | 14,832,203,896 | 12,681,534,331,080 | −12.244414% | dead |
| 5 | `wrappedShift` 263/203, existing physical tree | **invalid success** | 29 | 786,432 | 14,853,077,112 | 12,699,380,930,760 | −12.120916% | dead |

“Plausibly valid” means that the mathematical margin is large and a concrete proof route is
identified; it does not claim a Lean theorem or accepted certificate.

## 1. What `wrappedShift` accepts

For a left output `a`, right output `b`, widths `L,R`, and nonzero candidate `d`, define

\[
 A(a)=\left\lfloor\frac{2ra+2^L}{2^{L+1}}\right\rfloor
\]

and the inclusive natural-number interval

\[
 I_R(b)=\left[
 \left\lfloor\frac{2rb-r}{2^{R+1}}\right\rfloor,
 \left\lfloor\frac{2rb+r}{2^{R+1}}\right\rfloor
 \right],
\]

where the lower numerator uses truncated natural subtraction, exactly as protected
`numeratorInterval` does. At `b = 0`, the protected decoder unions this with `I_R(2^R)` to cover
the phase seam near one. Then, exactly,

\[
 d\text{ is returned}\quad\Longleftrightarrow\quad
 A(a)\ne0\pmod r\ \text{ and }\
 \exists q\in I_R(b)\cup(\mathbf 1_{b=0}I_R(2^R)),\quad q\equiv dA(a)\pmod r.
\]

This follows directly from `fixedCandidates`: it maps every such `q` to
`q * A(a)⁻¹` in `ZMod order`. The protected `take` does not truncate the set.

Consequences:

- It does **not** accept neighbouring right output bins. It accepts every group numerator whose
  ideal phase would round to the one observed bin `b`; exact half-bin ties can occur at both
  inclusive endpoints.
- The right ambiguity is a consecutive interval of about `r/2^R` numerators (two intervals only
  at the seam), each scaled by the same `A(a)⁻¹`. That is the “shift”; it is numerator ambiguity
  inside one bin, not a wider QPE success window.
- The left side chooses only the single rounded numerator `A(a)`. Increasing `L` makes that choice
  more reliable, but cannot remove the right nearest-bin bottleneck.

### Exact candidate budget

The official cap is

`56 * (2^49 + 2) = 31,525,197,391,593,584`.

For one trial, the protected limit is `2 * (order / 2^R + 2)`:

| R | Exact protected limit | Fits? |
|---:|---:|---|
| 202 | 36,028,797,018,963,970 = 2^55 + 2 | no |
| **203** | **18,014,398,509,481,986 = 2^54 + 2** | **yes** |
| 204 | 9,007,199,254,740,994 | yes |
| 208 | 562,949,953,421,314 | yes |

Thus **203 is the exact minimum right width**, not a range beginning at 204. The cap is about
`2^54.8`, not `2^55.8`.

### Why single-trial success fails

Conditioned on a character numerator `k`, the two QPE axes are independent. If the left rounds
to `k`, `wrappedShift` returns `d` on the right only when the right observation is the nearest bin
to `(dk mod r)/r`. Averaged over the permutation `dk mod r`, that nearest-bin mass tends to

\[
 \int_{-1/2}^{1/2}\operatorname{sinc}(x)^2\,dx
 = 0.7736950099028\ldots,
\]

independently of whether `R` is 203, 208, or larger. Making `L` large only makes the accepted mass
approach this value.

For a clean rejection bound, take `d=1` and split on whether `A(a)=k`. The latter failure has mass
at most `1/201` at `L=263` by the leader's sharp window lemma. The first case is the nearest-bin
event. Its exact point mass at centered residue `x` is
`(sin(πx)/(2^R sin(πx/2^R)))²`. On `[0,1/2]` this is decreasing up to a multiplicative
`1+O(2^(-2R))` finite-register correction; the centered `1/r` grid sum is at most its integral plus
one endpoint cell. Thus the finite-grid average is below 0.774, with margins vastly larger than
the `1/r` and `2^(-2R)` corrections. Consequently success is below
`0.774 + 1/201 + negligible < 0.779`. This analytic upper bound has not been ported to Lean,
because the numerical gap to 0.99 is decisive. The exact protected accepted set is given above;
evaluating its full `r`-term finite sum was not attempted.

**Left width verdict.** There is no left width, up to the protected maximum 512, that makes a
single `wrappedShift` trial uniformly 99% successful. `L=263` is enough to reuse the leader's
`200/201` left-window theorem and exposes the best resource projection; `L=262` could use the
averaged lemma below, but changes only 262 phase gates and not the 29-window count.

Carried lemmas: physical distribution and axis semantics carry; the 263-bit
`window_mass_sharp` carries on the left; `signedRow` and resource patterns are reusable.
`program_success` and the `nearestPair` decoder bridge do not carry. Risk is mathematical, not
engineering: the decoder's accepted event is too small.

## 2. How far `nearestPair` can drop

The leader proves a **pointwise** marginal window mass `200/201` from `2^t ≥ 128r`, then multiplies
the two conditional-axis masses. That condition first holds at `t=263`.

A sharper proof can average over characters before combining axes. Multiplication by every
nonzero secret permutes the character residues. If `W_t(k)` is the probability that an axis rounds
back to `k`, then `0≤W_t≤1` gives

\[
 \frac1r\sum_k W_t(k)W_t(dk)
 \ge 2\left(\frac1r\sum_k W_t(k)\right)-1.
\]

The nonzero-secret success sum drops the `k=0` character, costing exactly at most `1/r`; this is
immaterial to the displayed decimals but must be retained in Lean.

At `t=262`, `2^t/r` is just above 64. The large-order diagnostic is

| t | `2^t/r` | average marginal | permutation lower `2a−1` | `d=1` retained-window diagnostic |
|---:|---:|---:|---:|---:|
| 263 | ≈128 | 0.9984168761 | 0.9968337522 | 0.9968375116 |
| **262** | **≈64** | **0.9968338696** | **0.9936677392** | **0.9936827754** |
| 261 | ≈32 | 0.9936686777 | 0.9873373554 | 0.9873974779 |

The 262 margin above 0.99 is ample for finite-size rational bounds. A Lean route is to sum the
same double-cosine expansion used by Brief 08 over the whole rounding window, prove the averaged
marginal above 0.995, then apply the permutation inequality. The current pointwise
`window_mass_sharp` cannot simply be instantiated at 262.

At 261, even `d=1` is about 0.9874 before the tiny contribution from both axes landing in the same
wrong rounding window; a direct grouped-window diagnostic is about 0.98741. This is strong
evidence that 261 is impossible, but this brief does **not** claim a finite-order Lean upper-bound
theorem. Therefore 262 is the best proof target, not a proved optimum.

### When bit savings become a window

Dropping one bit from each axis (263→262) saves only

`2 * (263 - 1) = 524`

Fourier phase gates. It does not remove an addition. Under the 983,040-row cap:

- with widths up to 17, the first reduction from 33 to 32 signed additions occurs only at
  **258/258**, five bits removed per axis;
- using only widths at most 16, it occurs at **256/256**, seven bits removed per axis;
- a second signed addition disappears at **253/253**, ten bits removed per axis with width 17.

All of those precisions are far below the plausible single-trial success threshold. Re-packing
does make five-bit savings count, but it cannot turn the one-bit 262 theorem into a window cut.

Proof effort: **L**. Distribution, physical program semantics, `nearestPairCandidates`, and most of
the leader's `program_success` bridge carry. The new averaged marginal and character-permutation
composition replace `sharp_window_mass`/`success_of_window_mass`; layout positions and resource
literals must be regenerated.

## 3. Exact row-cap and lookup optimization

For a signed logical width `w`, the coefficient block has `2^(w-1)` rows. The leader's direct
16-bit load always costs 65,536 rows. Minimizing signed-window count first and rows second gives:

| Decoder/precision | Left after direct | Right | Signed windows | Total rows |
|---|---|---|---:|---:|
| `nearestPair` 263/263 | 9×15 + 7×16 = 247 | 9×15 + 8×16 = 263 | 33 | 851,968 |
| `nearestPair` 262/262 | 10×15 + 6×16 = 246 | 10×15 + 7×16 = 262 | 33 | 819,200 |
| `wrappedShift` 263/203 | 9×15 + 7×16 = 247 | 5×15 + 8×16 = 203 | **29** | 786,432 |
| `wrappedShift` 262/203 | 10×15 + 6×16 = 246 | 5×15 + 8×16 = 203 | **29** | 770,048 |

The 263/203 design cannot fit 28 signed additions: the minimum is 1,130,496 rows. Thus its four
saved additions are row-cap optimal for widths at most 17.

The present leader does **not** obtain cheaper T for its 15-bit windows: it aliases both halves of
the fixed 32,768-row `Physical.actual` tree, so every signed window costs 512,157,359 T after
dadon's 1,156,680-T cancellation patch. The exact correction lookup law in the source is

`91 * (nodes) + 85,848`, with `nodes = rows - 1`.

Keeping the arithmetic/cancellation part fixed gives the following conditional specialized costs:

| Signed width | Rows | Lookup T | Whole signed-window T |
|---:|---:|---:|---:|
| 15 | 16,384 | 1,576,701 | 510,666,415 |
| 16 | 32,768 | 3,067,645 | 512,157,359 |
| 17 | 65,536 | 6,049,533 | 515,139,247 |

This is an exact count formula, but not an implemented circuit. A specialized tree needs new
route/layout, coherent correction, `signedRow`, slots, support and resource proofs. Effort is
**M/L**. Generic correction semantics and the leader's `ipxCost` proof pattern carry; the hardcoded
`batchWindowTree`, `Physical.actual`, enum cases and numeric resource facts do not carry unchanged.

Width 17 is not needed by any valid design above. If used at 258/258, it also needs a 17th bank
bit. It may be possible to borrow the already-supported, restored zero flag 837 and reuse the
16-lane direct-load path, but that cleanliness/route claim is unproved; otherwise the qubit count
increases.

## 4. Combination accounting and risks

For the existing physical tree, with `n` signed additions, the exact leader-derived formula is

\[
T=458745+n\cdot512157359+\binom L2+\binom R2.
\]

For specialized trees, replace each signed term by the width-specific table above.

| Lever | Exact? | Proof effort | Leader pieces that carry | Main risk |
|---|---|---|---|---|
| `wrappedShift` R=203 budget and accepted-set characterization | yes | S | protected decoder definitions/cardinality | none in arithmetic; success is fatal |
| `wrappedShift` 263/203 success ≈0.774 | finite exact sum not evaluated; rejection bound analytic, not Lean-checked | M to formalize rejection, but no value | left rounding lemma, physical distribution | cannot reach 0.99 |
| `nearestPair` 262/262 ≥0.99 | numerical/proof route, not Lean-checked | L | decoder bridge, distribution, program structure | averaged finite-sum lemma |
| 15/16/17 row optimum | yes | S | coefficient-row accounting pattern | none |
| width-specialized lookup T | exact conditional formula | M/L | `ipxCost`, correction semantics | new trees/routes/resource replay |
| 262/262 + specialized lookup | exact resources conditional on two unproved components | L | both sets above | only −0.176%, below policy |
| 263/203 + specialized lookup | exact resources, **invalid certificate** | dead | resource pieces only | success ≈0.774 |

The practical conclusion is to **not build `wrappedShift`** and not pursue a 262-bit proof for the
current >10% policy. Width-specialized 15-bit correction trees are a real small T lever, but belong
in a stack with a larger arithmetic improvement rather than a standalone submission.
