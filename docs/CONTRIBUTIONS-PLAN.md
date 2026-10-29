# Contributions on top of the upstream streaming certificate

2026-10-29, Brief 05. **First prove an average-peak acceptance bound; next borrow arithmetic scratch during correction.** The former has a concrete mathematical route to six rounds; the latter has an explicit 3,622-label allocation. Together their conditional score is **312,796,817,698,212**, 4.70× better than Brief 04's accepted 26-round score. Neither improvement has been implemented or checked in Lean here.

This was source analysis and Python only. No bench edits, builds, `lake`, score, or submission were run by Brief 05. Baseline for comparisons: **3,932 Q × 374,227,740,666 T = 1,471,463,476,298,712**, 26 rounds, 256/208 Fourier bits, wrapped-shift decoder. Brief 04 recorded official acceptance during this analysis (`entrants/20261029-1149-streaming26`); that receipt, rather than an independent replay here, establishes the baseline.

Source pins: upstream `b46e3371587f2f947c833b665b2636a863b7d85f`; protected `origin/master` `5fbad2ca7d821393335fb7e659b4f62d30093a02`. Below, `C/`, `W/`, `O/`, `A/`, `E/` abbreviate `ShorECDLP/Submission/2607_13816/{Challenge,Window,OrderFinding,Arithmetic,EEA}/` at that upstream commit. Protected files have the same contents at the pinned master. Read them with:

```bash
git -C ~/shorecdlp show upstream/lamport/challenge-final-certificate:ShorECDLP/Submission/2607_13816/Challenge/WindowBody.lean
git -C ~/shorecdlp grep -n batchedResetWires upstream/lamport/challenge-final-certificate -- ShorECDLP/Submission/2607_13816
```

Reproduce arithmetic: `python3 workspace/round_mass.py` and `python3 workspace/streaming_t_breakdown.py`. These use the standard library, preserve integer residues before floating-point conversion, and assert the headline resource identities. Their numerical evidence is separate from proof evidence.

## Ranked candidates

Effort: S = local composition; M = several connected lemmas; L = substantial semantics/resource integration; XL = different arithmetic or correction architecture. Gains are relative to Brief 04 and are conditional unless labeled existing.

| Rank | Contribution | Q×T gain | Effort / risk | Prior work reused |
|---|---|---|---|---|
| 1 | Average nearest-peak mass, uniform over every nonzero secret; aim for **p ≥ 0.546**, six rounds | **4.333×**, score **339,568,494,530,472** at 3,932 Q | M/L; medium. Analytic minorant, finite residue sums and character reindexing need Lean proofs | No arithmetic transfer; our new acceptance proof layered on upstream distribution/decoder results |
| 2 | Correction-only bijection borrowing **310** clean arithmetic labels | **1.0856×** (7.884% less Q), score **1,355,452,876,692,252** at 26 rounds; combined with rank 1: **312,796,817,698,212** | L; medium. Component boundary cleanliness and frames must replace globally disjoint workspace invariants | sub870 owner/lane-loan discipline; R21 frame and support proof patterns |
| 3 | Exact phase-only compare / carry and repeated-AND specialization **inside the EEA**, after counting one concrete cell | Removing 10% / 25% of wrapper T would lower total T **8.666% / 21.665%** (1.095× / 1.277×). Sensitivity estimates, not measured gains | L; high until a compatible cell is identified | Gold `compare_phase_exact`, `carry_base_recipe`; C77 `ctx_holds.rs`; R21 phase-debt lemmas |
| 4 | Use existing measured equality/transposition builders in batch correction | **0.04453%** less T, **166,659,584 T** saved over 26 rounds; same Q | M; low/medium. Existing quantum lemmas, but new compiler counts and record positions | Exact 0-T AND cleanup; largely already available upstream |
| 5 | Cancel the adjacent equal sign-negation pair at coordinate/correction boundary | **0.008339%** less T, **31,207,904 T** saved over 26 rounds | S/M; low/medium. Equality of coherent action rather than branch-history lists | Involution/cancellation and phase-aware boundary reasoning; upstream already has negation involution |
| 6 | New correction without five resident endpoint words; target **855–870 Q** | At unchanged T: 4.52–4.60×. A naive streamed design is **worse** on score; no competitive T bound yet | XL; high. Must change the correction algorithm | Prior lane loans, small-space carries and ownership accounting; no prior full exceptional-correction proof |
| 7 | Make the numeric `163/1000` bound closer to `16/π⁴` | **No score gain**: both need 26 rounds | S; low | No prior transfer needed |

Ranks reflect credible certified gains, not only maximum hypothetical gain. Rank 4 is a useful small end-to-end pilot; rank 3 has the largest arithmetic opportunity but no justified fixed saving yet. Rank 2 is not a claim that physical relabeling can reach legacy width.

## 1. Why the support is 3,932, and what can actually be shared

`C/Reset.resetWires = range 837 ++ [838] ++ range' 855 16` has **854** distinct labels. `C/WindowBody.batchedResetWires` appends **2,565 + 512** labels, giving **3,931**. `C/CompleteSupport.completeBatchedSupport` adds **837**, the zero-divisor flag used by the zero-allowed field wrappers. Thus the union is **3,932**, not 854 plus 3,931. The prior inventory's shorthand must not be read as that sum.

| Labels after placement/address relocation | Count | Purpose / lifetime |
|---|---:|---|
| 0–836, 838, 855–870 | 854 | Original reset allocation, including data, EEA/arithmetic scratch, lookup path and current 16-bit address/sign bank |
| 837 | 1 | Zero-input detector for coordinate arithmetic; touched by `fig15ZeroPrepare/Restore`, coherently restored, omitted from original reset |
| 1024–3588 | 2,565 | Five 513-bit endpoint words: four source words and one reusable target |
| 4102 | 1 | Correction equality/transposition flag |
| 4103–4613 | 511 | Equality chain scratch for 513-bit words |

The abstract sixth word at 3589–4101 is **already reused**: `C/BatchPlacement.batchPlacement` maps it to x=263–518, y=580–835, infinity=838. It contributes no extra 513 wires. `W/AddressBank.windowAddressPerm 855` exchanges 839–854 with 855–870; it parks the same 16-bit bank across windows, not a new bank for every window or round. `pointLookupAddress` is 839–853 before relocation, and `pointLookupPath` is 519–533.

The bound is not merely an inflated dense interval: gaps 839–854, 871–1023 and 3589–4101 are absent. `CompleteSupport` proves an upper bound, not equality. For any positive number of rounds, however, reset explicitly measures every member of the 3,931-label list, and coordinate arithmetic touches 837 (`coordinateProgram_touches837`). That supplies a syntactic lower-bound argument for the unchanged program. Deleting dead reset operations can only help after the rest of the actual program's support is recounted.

**Lifetimes.** During coordinate evaluation, the EEA and multiply workspace is occupied; the endpoint bank is clean. After coordinate evaluation, scratch is clean again, the 513-bit transformed accumulator remains live, and the address/sign bank must remain coherent through correction. During correction, `batchSchedule` loads four source words and a target word, executes 16 transpositions and 14 queries, and unloads all five words. Source contents are temporarily changed and restored; they are not five independent disposable copies. The 511 chain bits and comparator flag are live during transpositions. The 15 lookup-path bits are used during queries and clean between them. The final sign negation then uses arithmetic scratch again, after correction has returned it clean.

Keeping the *entire* arithmetic scratch set disjoint from the *entire* correction workspace is proof convenience. Keeping all six resident words disjoint within this batch implementation is a real constraint. Label reuse between windows and rounds is already present.

### Explicit allocation: 3,622 labels, no extra T

Keep these correction boundary values/ports fixed:

- accumulator: 263–518, 580–835, 838 (**513**);
- bank: 855–870 (**16**, including sign);
- query control 836 and path 519–533 (**16**).

Of the original 855-label complete coordinate support, **855 − 513 − 16 − 16 = 310** labels are available. This includes 837, provided its zero/restore invariant is proved at the correction boundary. Take the first 310 labels of `1024–3588 ++ 4102–4613` and exchange them bijectively with those available labels. Apply this permutation **only to the placed correction component**, fixing every listed live port. The Python script constructs the involution, checks the global union, and obtains **855 + 3077 − 310 = 3622**. There are no physical SWAP gates: this is the wiring of a separately compiled component.

This reaches the minimum global support **within the class of a single injective relocation of this unchanged batch allocation**, with its fixed 15 distinct query-path wires and 16 preserved bank wires: six words (3,078) + comparator (512) + path (15) + query control (1) + bank (16) = **3,622**. This is not a lower bound for all equivalent circuits or all possible arithmetic.

Use a deduplicated reset allocation containing all 3,622 resulting labels for the simplest first implementation. The round record stride becomes **860,607,173** (309 fewer records; the old reset omitted 837). A later proof can omit clean scratch resets. T stays **14,393,374,641** per round. Do not retain resets on the displaced high labels: that would retain those qubits in the official union.

Further phase-local aliasing can share the 15 query-path labels with comparator scratch, targeting **3,607**. If the query control doubles as the clean comparator flag during swaps, X toggles can target **3,606**. Those are schedule designs needing new boundary invariants; they are not obtained from one global permutation. Savings beyond 3,622 are small. Under the six-word/full-chain architecture, six resident words plus 512 comparator lanes and a preserved 16-bit bank give the corresponding 3,606 peak allocation; this is an architectural count, not a universal quantum lower bound.

### Why 854/~870 requires a different correction algorithm

The endpoint words alone are **2,565** extra bits. Even replacing the 511-bit equality chain cannot fit the existing resident-word architecture in ~870 labels. Sequentially rematerializing only two endpoint words around the accumulator still leaves three 513-bit words before comparison scratch. A claim that renaming the current batched circuit reaches 870 is unsupported.

A space-first alternative can avoid endpoint registers: iterate table rows with fixed `whenBit` gates, test the selected row and accumulator against classical endpoint bits, perform a flag-controlled endpoint XOR, and clear the flag. Compare 529 address/data bits with a blocked AND tree: about 32 local carry wires plus 17 block flags fit comfortably in the original ~325 free arithmetic wires. `ExceptionalFields` supplies endpoint bits from constant masks and the allowed point fields. This makes a **conditional ≤855–870** support design plausible without a quantum endpoint bank. It does not prove a new total group-translation implementation.

The T tradeoff is unfavorable for the obvious construction. A full-chain proxy for 16 transpositions, four 529-bit equality tests each, 32,768 rows gives **15,487,467,520 T/window**, before additional space-saving overhead. This exceeds the entire old window's **514,030,776 T** by 30×. At 870 Q, the whole window must stay below about **2,323,247,244 T** merely to beat the 3,932-Q baseline at the same round count. Low-space leaf comparisons need batching/phase methods that overcome this gap. The direct row-loop proxy is a reason to reject that first design, not an impossibility theorem for a better correction circuit.

### Protected definitions and proofs affected

Do not edit protected `C/{WindowBody,BatchPlacement,BatchedEndpoint,Outer,Reset}.lean` or `W/AddressBank.lean`. For 3,622 Q, reuse their builders but define new Entrant terms for:

1. correction-only permutation and `compactPlacedBatchProgram/Source` (wrapping `placedBatchProgram/Source` with `relabelCompiled` / `AdaptiveCircuit.relabel`);
2. compact window segments, prepared window and actual left/right lists, since protected `batchedWindowSegments` hardcodes the old correction;
3. compact reset and `standardOuterPlan`, with a fresh layout/entry/cursor.

No change to `windowAddressPerm` itself is necessary. No change to the abstract `batchWord`, `batchSchedule` or arithmetic algorithms is necessary for this milestone. Phase-local 3,607/3,606 targets would require replacements for the hardcoded `batchOps` schedule lowering and its per-step readiness predicates too.

Redo the affected `BatchBoundary` clean/frame bridge and `PlacedBatch`/`BatchedWindowCoherent` composition, then the concrete `ActualWindow/WindowValidity`, cross-window/outer execution and round reset interfaces. Reuse generic relabel/coherent composition theorems and the abstract endpoint model. Redo support (`BatchSupport`, `WindowSupport`, `CompleteSupport`), counts/stride, positions/layout, `UniformT`, slot and resource assembly for the new producer. Much can be transported; equal T and equal abstract translation do **not** imply equal instrument histories. The old global `BatchedPointReady` asks for a disjoint clean workspace throughout coordinate evaluation, which is exactly the invariant that must be replaced with phase-specific predicates.

## 2. Acceptance: the real formula and the mass discarded by the proof

Write r for the group order, N=2²⁵⁶, M=2²⁰⁸. `O/PeakMass.paperPhaseAmplitude` defines

\[
A_L(t,a)=L^{-1}\sum_{x=0}^{L-1}e^{2\pi i x(t-a/L)}.
\]

`O/AsymmetricPair.asymmetricPairMass` gives the exact output law

\[
P_d(a,b)=r^{-1}\sum_{k=0}^{r-1}|A_N(k/r,a)|^2
 |A_M((dk\bmod r)/r,b)|^2.
\]

The true accepted mass is **the sum of this expression over the outputs whose wrapped candidate list contains d** (`reducedCoverageMass`, `reducedVerifiedMass_eq`, `DecoderBridge.wrappedIdeal_mass_eq`). It depends on d. There is no one exact acceptance value specified by “256/208 bits.” Evaluating the full secp256k1 sum directly is infeasible here; no full-mass numerical value for all secrets is claimed.

The expression actually bounded in `secpSuccessBound_numeric` is

\[
B=\frac{r-1}{r}\left(\frac4{\pi^2}\right)^2
 =\mathbf{0.164255716075\ldots}.
\]

This is the **true numerical value of the existing analytic lower bound**, not of the accepted event. Raising 0.163 to B cannot reach the 25-round threshold **0.168236228897…**.

Where mass is lost:

1. `O/ReducedCoverage.reducedCoverageMass_lower` retains one nearest pair for each nonzero k, dropping every other accepted output.
2. `O/AsymmetricPair.asymmetricPairPeak_mass` drops all other character-mixture summands at each selected output.
3. `paperPhasePeak_mass` / `reducedPeak_mass` replace both actual nearest-peak probabilities by their worst case **4/π²≈0.405285**. This is the large avoidable loss.
4. `W/Repetition.secpSuccessBound_numeric` bounds `(r−1)/r` by 999/1000 and `4/π²` by 81/200, then rounds to 163/1000. This last rational slack is small.

For nearest rounding, let δ be the signed bin residual in [−1/2,1/2]. Its exact peak mass is

\[
f_L(\delta)=\left(\frac{\sin(\pi\delta)}{L\sin(\pi\delta/L)}\right)^2
 \ge f(\delta)=\operatorname{sinc}(\delta)^2.
\]

The continuum average of f is **0.773695009903…**. Squaring it gives **0.598603968349…**, a useful diagnostic under independent phases. **The two residues are related by d; independence is unavailable for a certificate valid for every secret.** For example, d=2⁴⁸ makes the two bin residuals coincide, and the nearest-pair average approaches the integral of f² instead.

The script's 50,000-sample nearest-pair-subset estimates are approximately 0.60035±0.00092 at d=1 and 0.63379±0.00122 at d=2⁴⁸ (standard errors, not certified bounds). Full small-prime enumeration, r=31, n=5, m=3, gives accepted mass 0.756347 at d=1 versus 0.635368 at d=7. The latter is a demonstration of secret dependence, not a secp256k1 approximation. The script labels subset samples and full enumeration separately.

### A uniform six-round bound without independence

For nonzero d, multiplication by d permutes the r characters. Since r is odd prime, multiplication by 2²⁵⁶ and by 2²⁰⁸ also permutes residues. Consequently **both centered residual marginals are exactly uniform on j/r, −(r−1)/2≤j≤(r−1)/2**, irrespective of their correlation.

Use `uv ≥ u+v−1` for probabilities u,v in [0,1]. If a is a lower bound on either average nearest-peak mass, then the retained nonzero-character subset has mass at least **2a−1−1/r**. The continuum value is 0.547390019806…, but an integration theorem is unnecessary for a sufficiently strong certificate. On |x|≤1/2 use the polynomial minorant

\[
f(x)\ge 1-\frac{\pi^2x^2}{3}
  +\frac{2\pi^4x^4}{45}-\frac{\pi^6x^6}{315}.
\]

It follows from the one-sided cosine Taylor bound through degree eight, using `sin² t=(1−cos 2t)/2`. Prove that analytic inequality in Lean; numerical sampling does not establish it. The three finite even moments have exact rational Faulhaber formulas. With π in (3.1415,3.1416), choosing the conservative endpoint for each sign, the script obtains

\[
a\ge0.773140157140\ldots,\qquad
2a-1-1/r\ge0.546280314281\ldots>\frac{546}{1000}.
\]

Thus **p≥0.546 is a concrete proposed theorem**, not a Lean result. It would give `1−(454/1000)^6 = 0.991243407954631…`; five rounds would only give 0.980712… at this bound. Required work is M/L: a new analytic bound and finite sums, not a new quantum circuit. A weaker polynomial minorant is a useful intermediate 7–8-round milestone if the degree-eight cosine proof is awkward.

| Per-round lower bound p | Required rounds | T bound | Status |
|---:|---:|---:|---|
| 0.163 | 26 | 374,227,740,666 | Upstream theorem |
| 0.164255716075… | 26 | 374,227,740,666 | Existing analytic expression |
| 0.20 | 21 | 302,260,867,461 | Implied if proposed stronger theorem succeeds |
| 0.25 | 17 | 244,687,368,897 | Same |
| 0.30 | 13 | 187,113,870,333 | Same |
| 0.40 | 10 | 143,933,746,410 | Same |
| 0.50 | 7 | 100,753,622,487 | Same |
| **0.546** | **6** | **86,360,247,846** | Proposed uniform polynomial proof |
| 0.60 | 6 | 86,360,247,846 | Optimistic research target, no uniform proof |
| 0.70 | 4 | 57,573,498,564 | Speculative; no support from this analysis |

Five rounds need **p≥0.601892829447…**, already above the independent-phase diagnostic. Do not budget five rounds from a sampled mass “about 0.6.”

### Does changing rightBits help?

The current layout and bridge use wrappedShift with exactly 256/208 bits; changing bits is a new layout/producer proof, not a parameter change to the existing theorem. The protected `Challenge/Decoder.trialCandidateLimit` is `2*(order / 2^rightBits + 2)` and the total cap is `56*(2^49+2)`.

| rightBits | Maximum trials under candidate budget | Consequence |
|---:|---:|---|
| 192 (12 full banks) | 0 | Cannot remove one complete right window, even with one trial |
| 204 | 3 | Cannot support six trials |
| 205 | 7 | Six trials fit, but still need 13 banks with a partial last bank |
| 206 | 14 | Six trials fit, same arithmetic-window count |
| 207 | 28 | 26 trials fit, same arithmetic-window count |
| 208 | 56 | Current layout |
| 209–224 | ≥111 | Needs a partial/additional bank; no improvement to the present worst-case bound |

Right precision does not improve the uniform nearest-peak lower bound: the residue permutation and limiting sinc law are unchanged at these large sizes. Reducing 208 to 207 saves at most **207 Fourier phase slots per round**, not a 514-million-T arithmetic window. Reducing to 205 after a six-round proof saves only **618** phases/round. Both require replacing the hardcoded 16-bit-bank interfaces. Increasing to 224 would add an addition window and exceed the current table cap (983,040 rows, already exact) with the existing window scheme. A new table/window design could change that tradeoff, but is not a free precision improvement.

## 3. Exact T breakdown and specific arithmetic transfers

`C/UniformT.batchedOuterPlan_round_t_uniform` proves the uniform upper bound. Its arithmetic identity is

**458,745 + 28 × 514,030,776 + 54,168 = 14,393,374,641.**

The first window is a smaller 16-bit point lookup. There are 15 left and 13 right addition windows. Sign-address preparation, Hadamards and resets add zero T. The Fourier term is the all-enabled bound `256*255/2 + 208*207/2`; an individual instantiated history can use fewer P gates.

| Component | T per addition window | T per round | Fraction of round |
|---|---:|---:|---:|
| Four measured EEA forward/reverse wrappers | 445,480,420 | 12,473,451,760 | **86.6611%** |
| Six Horner multiply/unmultiply calls | 46,642,386 | 1,305,986,808 | 9.0735% |
| Two zero-allowed prepare/restore pairs | 14,252 | 399,056 | 0.00277% |
| Square/subtract | 15,567,153 | 435,880,284 | 3.0283% |
| Ten coordinate QROM traversals | 2,293,690 | 64,223,320 | 0.4462% |
| Five coordinate modular lookup adders | 98,455 | 2,756,740 | 0.01915% |
| Five internal coordinate negations | 107,170 | 3,000,760 | 0.02085% |
| Two extra sign negations | 42,868 | 1,200,304 | 0.00834% |
| Fourteen correction QROM traversals | 3,211,166 | 89,912,648 | 0.6247% |
| Sixteen correction transpositions | 573,216 | 16,050,048 | 0.1115% |
| First lookup | — | 458,745 | 0.00319% |
| Fourier feedback bound | — | 54,168 | 0.000376% |

Sources: `W/LookupPrimitiveCounts.signedCoordinatePrimitives`, `A/InPlacePrimitiveCounts`, `E/MeasuredPrimitiveCounts`, `C/{WindowCounts,BatchCost,WindowBudget,UniformT}`. In each zero-allowed field operation, **2×15,910,015 EEA CCX + 3×1,110,533 multiply CCX + 1,018 zero-wrapper CCX = 35,152,647 CCX**. One square contributes 2,223,879 CCX. A modular lookup adder contributes 2,813 CCX, each negation 3,062 CCX. This accounts exactly for 72,886,218 coordinate CCX and 510,203,526 T.

The **3,784,382-T** correction is `14*7*32767 + 16*35826`. Each 513-bit transposition contains four equality tests at `7*(2*513−3)` T and 2×513 update CCX. Endpoint payload CX gates cost zero T; there is no benefit from treating these table words as paid rotations.

**AND erasure.** The prior `Gold/source/arithmetic.py:and_uncompute` and C77 `ctx_holds.rs` match the benchmark's measurement-uncompute idea. `E/DecoderPrimitiveCounts.measuredAndErase_primitive` already prices erase as **0 T + one measurement**, with CZ implemented by H/CX/H. Both coordinate/correction QROM trees already use one paid CCX per internal node and a free measured erase. Applying that same transformation to those nodes saves **zero** additional T.

There is an actual unused opportunity in correction's ordinary unitary equality chains. `C/RegisterEquality.registerEqualAdaptive` and `endpointTranspositionAdaptive/Program` already implement and prove measured alternatives, while `BatchedEndpoint.batchOps` lowers `.swap` as `ordinaryOp (batchOpCircuit ...)`. Replacing it saves **511 CCX / equality**, 64 equalities/window, hence **228,928 T/window** and **32,704 extra measurements/window**. Over 26 rounds it adds **23,808,512** records, comfortably within the current cap's ~25.10-billion margin. New cursors, producer support/slots and coherent batch composition are still required. This is a compositional improvement using an existing primitive, not a novel AND-erasure theorem.

**Phase-only carries and holds.** Gold `compare_phase_exact` emits a comparison's measured phase directly; C77 `ctx_holds.rs` shares repeated AND values with a clean donor, saving **7(k−1) T** for k identical products plus one measured cleanup. Apply these only where EEA control/repair logic needs a phase or where source-level control forms are provably repeated. EEA length and interval predicates that steer later steps still need usable classical/quantum values; they cannot all be replaced by phases. Start in `C/{MeasuredStep,MeasuredWrapper,LengthRefresh}`, `E/{MeasuredStep,MeasuredSchedule}` and the `A/Gidney*` arithmetic they call. Count the selected cell in the actual 1,620-step schedule before claiming any fraction of the 86.66% wrapper cost. Conditional 10%/25% wrapper reductions save **1,247,345,176 / 3,118,362,940 T per round**. C77's archived 10,502-CCX/CCZ saving is for its different point-add stream and is not evidence for those rates here.

**Cheaper adders.** Gold's exact `chunk_add` no-carry-out n-bit construction costs **7(n−1) T**, n−1 carry measurements and n−1 clean carries. At n=256 that is 1,785 T and 767 isolated wires. Existing 256-bit controlled constant adder counts are 764 CCX, and the lookup modular-add block totals 2,813 CCX. Those implement control, modular reduction, comparisons and low-room dirty-lane interfaces that the simple adder lacks. Therefore subtracting 1,785 from the full modular-adder price is invalid. Borrowing the 3,077 idle correction lanes could supply carries during coordinate arithmetic, but requires another phase-specific layout proof. Whole-entry savings should be sought in frequently repeated EEA/Horner adds; the five outer modular adders together are only **0.01915%** of round T even if eliminated entirely.

Prior source locations inspected for this brief: `/mnt/c/code/secp256k1-point-add-spooky/.workspace/routes/ecdlp-gold-leapfrog-v1/source/arithmetic.py`, C77 `.../sub870-v1/lp-variants/c77-final/src/point_add/ctx_holds.rs`, and `/home/gitzard/r21-lean/opus-inv/gatecut/GatecutB.lean` (`hmr_pay*`, phase-debt/frame patterns). Follow [RELATED-WORK.md](RELATED-WORK.md) for provenance and native-proof caveats. Reuse exact algorithms/invariants, not archived `bv_decide` proof assumptions or sampled-mean Toffoli costs.

## 4. Concrete implementation briefs for the top two

Brief 04 also discovered that the official source gate rejects untracked or unreachable Lean files. The logical modules below should be developed in a lab-side modular tree, then folded into the existing tracked Entrant files with `workspace/package_streaming.py`, as Brief 04 did. Adding new physical files under Entrant requires the human/orchestrator to track them first; this analysis does not authorize Git metadata writes or assume the gate will accept untracked modules. Existing modular source is preserved in `entrants/20261029-1140-streaming26-modular`.

### Outline A: uniform averaged peak mass, six streaming rounds

**Deliverable:** unchanged 3,932-Q circuit body, six repetitions, wrappedShift 256/208 layout, T≤86,360,247,846, measurements=**5,163,644,892**, ≥99% success for every nonzero secret. First milestone is a kernel-checked standalone mass theorem; do not modify the repetition count until it exists.

Add under `ShorECDLP/Submission/Entrant/Contributions/` in a fresh namespace:

- `SincPolynomial.lean`: one-sided cosine/Taylor bound, sinc minorant, normalized amplitude lower and upper bounds, including δ=0.
- `CenteredResidues.lean`: multiplication permutations for odd prime r, nearest-bin signed residues, exact second/fourth/sixth sums. Prove general lemmas, specialize rational arithmetic to the fixed group order.
- `AveragePeakMass.lean`: sum the latent-character nearest-pair contributions, use `uv≥u+v−1`, remove k=0, derive `546/1000 ≤ reducedCoverageMass order 256 208 d` for `d % order ≠ 0`.
- `SixRoundSuccess.lean`: replace the numeric lower bound at `DecoderBridge`/`RepeatEvent`, propagate through actual round success/reset/retry theorems.
- `SixRoundCertificate.lean`: define consistent six-round entry/layout/bounds and final certificate; adapt Entrant/Main only after all checks.

Reuse protected `O/{PeakMass,ReducedPeak,AsymmetricPair,WrappedCandidates,ReducedCoverage,ReducedVerified}`; upstream port's `DecoderBridge.wrappedIdeal_mass_eq`, `IdealDistribution`, `RoundReset`, `RepeatEvent`; generic independent-retry monotonicity, existing uniform T/slots/support/count lemmas. Avoid duplicating the Fourier circuit implementation.

Proof obligations: (i) analytic polynomial minorant with no native axioms; (ii) exact finite residue reindexing on both axes, with d tied to the nonzero public point; (iii) nearest-pair decoder completeness and injection, or equivalent rearrangement of the full character sum; (iv) uniformity in the secret, not independent-residue assumptions; (v) actual round mass and clean reset bridge; (vi) six-round records/layout and all budgets. The rational success power can use `norm_num`. Protected old `secpSuccessBound_numeric` stays untouched.

Acceptance checks after Brief 04 relinquishes the bench: build the new theorem chain, inspect allowed axioms, boundary check, official score and snapshot. Stop if the exact polynomial/moment bound falls below the six-round threshold; record a proved seven/eight-round improvement rather than weakening the claim informally.

### Outline B: borrow 310 arithmetic labels during correction

**Deliverable:** preserve the baseline translation and T, reduce complete support to **3,622**, then stack on the accepted mass improvement if available. Use the explicit involution from `workspace/streaming_t_breakdown.py` as the allocation specification.

Add under `Entrant/Contributions/`:

- `CompactBatchLayout.lean`: finite swap permutation, fixed live ports, injectivity, disjoint resident words, image-support and 3,622-label union proofs.
- `CompactBatchBoundary.lean`: separate coordinate-ready, correction-ready and post-correction predicates. Prove exactly the borrowed lanes are clean on entry and restored on exit; keep x/y/infinity and bank coherence throughout.
- `CompactBatchWindow.lean`: relabeled correction, new segment/prepared/actual windows, source execution and coherent total point translation on all valid points, including infinity and exceptional additions.
- `CompactOuter.lean`: new window lists/reset/plan, stride **860,607,173** if all 3,622 labels are reset; new absolute Fourier positions.
- `CompactResources.lean`: syntactic support, measurement counts, uniform T, slots, candidate/table bounds.
- `CompactCertificate.lean`: instantiate the generic assembly with the new producer and update Main after official acceptance.

Reuse `Relabel.relabelCompiled_run`, `.relabel` for `CoherentlyImplementsOn`, `batchPlacement_data`, abstract `batchUnitary` and endpoint correctness, coordinate cleanup/frame results, `sequenceProgram`/`surroundCompiled`, `standardOuterPlan`, generic outer records/resources and retry lemmas. Keep the original program available for comparison; do not shadow protected declarations under their old names.

Proof obligations: (i) equal abstract point action after the component-only permutation fixing live ports; (ii) frame for borrowed scratch at both boundaries rather than a false all-phases-clean invariant; (iii) no lost or aliased resident word/control; (iv) syntactic support with displaced high-wire resets removed; (v) fresh cursor/decoder-position proofs and round reset; (vi) transport total mass/retry and resource obligations to the new producer. A single permutation of the entire old program would preserve its 3,932 distinct labels and achieve nothing.

For the first score, use the conservative full compact reset list and retain the original correction's gate/measurement structure. After acceptance, consider phase-local path/comparator sharing separately. Do not attach the speculative 870 target to this brief's acceptance criteria.
