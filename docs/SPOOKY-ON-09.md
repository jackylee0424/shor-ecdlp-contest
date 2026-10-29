# Spooky pebbling on top of brief 09

2026-10-29. Read-only source analysis plus a Python calculator. No lake/Lean build, no bench edit, no submission.

## Verdict

1. **Spooky pebbling does not stack on the endpoint bank.** For the upstream conjugation schedule, an exhaustive pebbling search allows free X-measure/discard and recomputation of any word. Even then, 5 resident 513-bit words are needed (`workspace/spooky_endpoint.py` §2). The peak occurs while words are being computed (forward τ₃ conjugation, ops 0–4), not while they are being uncomputed. Brief 09 therefore stays at **3,111 Q × 86,437,092,390 T = 2.689e14**. Spooky gives ΔQ = 0 and ΔT ≥ 0.
2. Raw table words (s₃ and every tₖ) can already be unloaded and reloaded for 0 T by folding them into existing queries. Spooky never beats that. For conjugated words (u₀..u₂), the phase repair (−1)^{m·u(row)} is a non-linear function of table constants. A `whenBit` leaf cannot express it, so repairing it means replaying the forward conjugation. That costs about 3.1M T per window, against 1.76M T for the backward half it would replace.
3. **The analysis did find something bigger, and it replaces brief 09 rather than stacking on it.** The correction does not need a resident endpoint word at all. To compare the accumulator with a table column, XOR the column into the accumulator itself with an ordinary query (leaf CX gates, 0 T), zero-test it, then chain to the next column. Use four one-hot flags. **Design prediction: 855 Q × ≈86.24e9 T ≈ 7.37e13.** That is 3.65× better than the brief 09 projection and 4.6× better than the live 3.40e14, with slightly *less* T than today. Effort: **L**, medium risk. It is not verified. See §6.

Labels: *checked here* means the calculator asserted it. *Source* means it was read in upstream code. *Guess/design* means unverified.

Sources: upstream `upstream/lamport/challenge-final-certificate` (`U/` = `ShorECDLP/Submission/2607_13816/`). The local copies read are in `workspace/spooky_src/` (dumped by `workspace/spooky_dump*.sh`). Bench framework file: `ShorECDLP/Framework/Quantum/MeasurementUncompute.lean`.

## 1. What the batch correction does (source)

- **Storage.** `U/Challenge/BatchedEndpoint.lean`: `batchWord base j i = base+513j+i`. Words 0–3 are sources, word 4 is the reusable "b" word, word 5 is the data word, placed onto the accumulator by `BatchPlacement.batchPlacement`. `batchFlag = base+3078` and `batchScratch` are 511 wires.
- **Loading.** Every load is a **table lookup (QROM)**, never a copy from the accumulator. `batchLeaf` / `batchLeafCircuit` = `tableXorGates control (endpointRawMask read ports)`, which are leaf-controlled CX gates selected by `whenBit` on protected `PointField` bits. Column j of the row is `exceptionalEndpointWords row j` (`U/Challenge/EndpointLoad.lean`). Columns 0–3 are s₀..s₃ = F(0), F(C), F(−C), F(−2C), where F is the fig14 coordinate image (`ExceptionalFields.protectedExceptionPairs`). Columns 4–7 are t₀..t₃ = enc(C), enc(2C), enc(0), enc(−C).
- **Query cost.** One query costs `batchQuery_tCount` = 7·32,767 = **229,369 T** and 32,767 measurements. The cost is independent of how many words a query writes. One query can therefore load several columns, or XOR a difference of columns, for free.
- **Schedule.** `batchSchedule` has 30 ops: 14 queries (`batchSchedule_queries`) and 16 `swap source target` ops. The swap `endpointTranspositionCircuit` (word source, word 4, word target) applies Equiv.swap(W_src, W₄) to W_target. It runs two equality tests, then the word update, then two tests again (`endpointTransposition_correct`). Each swap costs 35,826 T (`batchOpCircuit_tCount`). The window total is 3,784,382 T (`placedBatchSource_tCount`), 0.736% of a round.
- **Semantics.** The forward half (ops 0–17) applies τ₃=(s₃,t₃), then τ₂'=(u₂,t₂), τ₁', τ₀' to the accumulator, where u_j is s_j conjugated by the earlier transpositions. The backward half (ops 18–29) restores W₀..W₂ to raw s_j so that the final shared query can XOR them out (`batchModel_data`, `batchModel_clean` in `BatchState.lean`).
- **Lifetimes** (op index, role: a = source, b = word 4, W = written), from calculator §1:
  - W3 (raw s₃): load 0, read 1–4 and 26–28, unload 29. It is never written.
  - W2: written 1 and 28, read 7–9 and 22–23.
  - W1: written 2, 7, 23, 27; read 12, 13, 19.
  - W0: written 3, 8, 12, 19, 22, 26; read 16.
  - W4 holds t₃, t₂, t₁, t₀, t₁, t₂, t₃ in seven lifetimes.
- **Last use.** W0 last does forward work at 16, W1 at 13, W2 at 9, W3 at 4. Every later use exists only to undo the conjugation.
- **Recompute cost.** A raw column costs 0 T when folded into a neighbouring query, or 229,369 T as a standalone query. A conjugated u_j costs a load plus j′ replayed swaps (each 64,414 T with the dirty comparator) plus their tₖ loads. u₂ ≈ 1 swap and 2 queries; u₀ ≈ 3 swaps and 6 queries.

## 2. Spooky schedule and peak residency

- **Lower bound (checked here, model-limited).** `min_resident_words()` runs a BFS over register contents {tₖ, s_j after d conjugators}. Its moves are: load a raw column; discard any word for free (spooky with repair cost ignored); apply τ'ₖ when uₖ and tₖ are resident. The minimum is **5 words**. Intuition: u₀'s last step needs u₁ and t₁. Computing u₁ needs 4 words: u₂ and X₁ under τ₃ need s₃ and t₃. Either X₀ or u₁ is held across that. The bound is limited to this algorithm family; §6 leaves it.
- **Best spooky schedule.** W3 can be X-measured after op 4 and re-created in the op-25 query. Coherent unload/reload folded into the op-5/op-25 queries costs the same 0 T and needs no repair, so spooky adds nothing there. Ops 1–4 still hold 5 words.
  - To measure W0..W2 and delete the backward half, the repair would need the phase (−1)^{m·u_j(row)}. u_j = τ₃(s₂) etc. involves the predicates [s₂=s₃] and [s₂=t₃] over 513-bit constants. `TemplateGate.whenBit` takes one constant bit and does not nest (`ShorECDLP/Challenge/Template.lean`), and `PointField` is a fixed protected enum. So no phase-lookup or derived-column repair exists. Recomputing into a register means replaying the conjugation.
- **Peak and donors.** The peak stays at 5 words. All four non-target words stay resident during every swap, so brief 09's donor accounting (511 donors drawn from the other endpoint word) is unchanged.
- **Qubits after brief 09.** 3,111, unchanged.

## 3. T, measurements, Q×T for spooky-on-bank

- **Q.** 0 change.
- **T.** Deleting the backward half saves 6 queries and 6 swaps (1,762,698 T/window with dirty swaps). Repairing W0..W2 by recomputation adds ≈3,138,912 T/window (rough lower estimate, calculator §3). Net **+1.38M T/window, about +38.6M T/round**.
- **Measurements.** About +1,539 records per window for the X-measures, which is far under the cap.
- **Gate slots.** They would change through new record positions.
- **Verdict.** Q×T gets worse (≈2.69e14 → ≈2.70e14). **Not a net win; do not implement.**

## 4. Proof obligations if spooky-on-bank were pursued anyway (not recommended)

- **Bench lemmas.** `measureResetWithCorrection_coherent` and `recomputeMeasurementUncompute_coherent[_of_classical]` only cover an *immediate* compute;Z;compute† with a unitary `Circuit` compute. Queries are adaptive (`unaryAction` has measurements), and the repair is deferred across other ops. That needs a new deferred phase-debt lemma, for example ported from `F/lean/SpookyLever/Quantum.lean` (`deferred_fix`) or `GatecutB.hmr_pay`; see `docs/RELATED-WORK.md`.
- **What would need redoing.** `batchModel_data` / `batchModel_clean` move to a new schedule model, along with `batchUnitary_schedule` (whose total "other words clean" postcondition breaks), BatchReady, the record count `batchedEndpointProgram_count` (14·nodes → +X records), Positions/decoder offsets, `UniformT`, `BatchSupport`, and slots.
- **Effort.** M/L for zero gain.

## 5. Other places spooky could stack on brief 09

- **310-loan workspace.** It is already clean at the correction boundary, and the loans are a pure relabel with 0 T. There is nothing to measure.
- **EEA divide.** As found earlier, the divide does not yield to spooky: the junction lower bound in R005 / `docs/spooky-theory.md` holds. The EEA wrappers are 86.7% of T.
- **Multiply checkpoint (R005 MSC).** It roughly breaks even, and stays that way here. While the 2,565-word bank dominates support, the 855-label core is not the bottleneck. After the §6 redesign, the core *becomes* the bottleneck, but its peak is set by the EEA/divide phase, so a multiply checkpoint still saves no labels (the same result as R005, where the cap stayed at 1,236).
- **Address/sign bank (16).** It must stay coherent through the correction; the Fourier step consumes it later.
- **Where spooky does help.** Inside the comparator. The AND-tree temporaries in §6 are measurement-erased (Gidney temporary AND, `EEA/MeasuredAnd.measuredAndErase_coherent_uncompute`). This is already priced into §6.

## 6. The alternative found: flag-only correction (no endpoint words) — DESIGN, unverified

**Key fact (source).** `fixedMatching_comp` / `fixedExceptionSwaps_correct` give π(F P) = T P for every point P, and F P = T P when P is not exceptional (`FixedMatching.lean`). So on a valid accumulator acc = F(P), the matching permutation is simply "if acc = sₖ then tₖ, else unchanged". The conjugation chain exists only to make the circuit total on *all* 2^513 words with possibly repeated pairs.

**Circuit, per window** (calculator §4):

1. **Flags.** For k = 0..3, set fₖ ^= [acc ⊕ sₖ(row) = 0]. Each "XOR column into acc" is an ordinary unary query whose leaf CX gates target the accumulator wires (0 T in the leaves). The queries chain: s₀, s₀⊕s₁, s₁⊕s₂, s₂⊕s₃, using two `whenBit` gates per bit. The zero test is X-conjugation plus a 513-control MCX into fₖ.
2. **Update.** acc ^= fₖ·(sₖ⊕tₖ)(row) through four queries with **fₖ as the unary-iteration control**. `runLeafState` ANDs the control into the path, so the query is genuinely controlled. The cost is the same 7·nodes.
3. **Clear.** fₖ ^= [acc ⊕ tₖ = 0], again with chained queries. The "XOR s₃ out" and "XOR t₀ in" steps merge across the update, because constant XORs commute with the flag-controlled XORs. That gives **13 queries and 8 zero tests**.

**Correctness sketch (guess-level, needs Lean).**
- The sₖ are distinct (F is injective, and 0, C, −C, −2C are distinct when 2C≠0 and 3C≠0, which holds for prime-order secp256k1 with C≠0). So at most one flag fires.
- An unmatched acc = F(P) = T(P) is never some tₖ, because T is injective. A matched acc becomes tⱼ, which differs from every other tₖ. So the clear step zeroes every flag.

**Comparator and width.**
- Live during the correction: acc 513 + bank 16 + control 1 + path 15. That leaves exactly the **310 clean** labels from `docs/CONTRIBUTIONS-PLAN.md` §1.
- A clean V-chain would need 511 scratch, which does not fit. Use a split instead:
  - a half chain over 257 bits with clean temporaries and measurement erase;
  - plus a dirty chain over the other half (`workspace/DirtyMCX.lean` `dirtySweep_run`, so brief 09's lemma is reused).
- That is about 1,300 CCX per test (guess). The pessimistic option, four half-size dirty MCXs with one borrowed ancilla, is 4,080 CCX.
- The 4 flags plus ≤256 temporaries fit in the 310. **Support = 855** (the core, including 837). No 1024–4613 labels remain.

**Numbers** (`python3 workspace/spooky_endpoint.py`; "x09" is the improvement factor over the brief 09 projection):

| Variant | Window T | ΔT/round | Total T (6 rounds) | Q×T | x09 |
|---|---:|---:|---:|---:|---:|
| 13 queries, 1,300 CCX test | 3,054,597 | −20,433,980 | 86,237,643,966 | **7.373e13** | 3.65 |
| 13 queries, 4,080 CCX test | 3,210,277 | −16,074,940 | 86,263,798,206 | 7.376e13 | 3.65 |
| 18 queries, 4,080 CCX (slack) | 4,357,122 | +16,036,720 | 86,456,468,166 | 7.392e13 | 3.64 |

Measurements ≈5.16e9, essentially unchanged and well under the 47.47e9 cap. T barely moves, because the correction is <1% of a round. The win is entirely Q: 3,111 → 855.

**Risks and open checks:**
- (a) **Validity.** The construction is correct only on valid accumulators. Upstream `batchUnitary_schedule` is total, so a validity predicate (acc = F(P) for the row's C) must be threaded through `BatchedWindowCoherent` / `WindowValidity` / `CrossWindowPoint`. Upstream's `batchUnitary_finite` already uses that hypothesis form.
- (b) **Infinity rows.** `batchUnitary_infinity` (C = 0) uses `normalizedEndpointWords`. If those pairs are not sₖ = tₖ, the one-hot formula gives the wrong answer. `whenBit` cannot gate a 2-constant condition. Check `normalizedEndpointWords_zero_action`, or prove that C = 0 rows are excluded for Q ≠ 0 (guess: they are unreachable for nonzero Q, since rows are odd multiples a·G / a·Q).
- (c) **Distinctness.** A Lean lemma that 2C, 3C ≠ 0 is needed (group order prime).
- (d) **Normalized vs raw words.** `protectedExceptionPairs_eq` covers C ≠ 0.

**Proof work (effort L).**
- **New component.** A new Entrant correction model replaces `batchSchedule` / `batchModel_*`, with flag invariants and the query-chain XOR lemma. Reuse `unaryAction_coherent`, `tableXorGates`, `endpointSelectGates_source`, `readEndpointWords_correct`, `fixedMatching_comp`, and DirtyMCX + `MeasuredAnd` for the zero test.
- **Window and support.** New window segments and prepared/actual windows. Drop `BatchPlacement`'s relabel. The reset list becomes the core list (`batchedResetWires` shrinks by 3,076).
- **Records and resources.** New record count 13·nodes + erasures, stride and positions, `UniformT`, slots, `CompleteSupport` = 855, and resource assembly. Transport the acceptance proof unchanged.
- **Brief 09.** The 310-loan step becomes moot. The dirty-MCX lemma is still needed.

**Recommendation.** Pause brief 09 step 2 (310 loans). First run a short paper check of risks (b)–(d). Then brief the flag-only correction as the next qubit step: target 855 Q, Q×T ≈ 7.4e13.

## 7. Paper check (risks a–d, resources, records)

**Verdict: GO, at effort L.** No blocking risk was found.
- Infinity rows are harmless as they stand.
- The validity hypothesis already exists upstream, at the `signedBatchSource` boundary.
- Distinctness is a short (S) lemma built from `order_prime`.
- The resources fit in the 310 clean labels.

Exact prediction (`python3 workspace/spooky_endpoint.py`, §7):

| Quantity | Value |
|---|---|
| Window T | **3,053,253** (was 3,784,382) |
| T per round | −20,471,612 |
| Total T (6 rounds) | **86,237,418,174** |
| Q×T | **855 × 86,237,418,174 = 73,732,992,538,770 (7.373e13)** |
| Total measurements | 5,158,465,644, which is 10.87% of the cap |

This is still a construction-level prediction. Nothing here was checked in Lean. Sources are in `workspace/spooky_src/`, dumped from upstream `b46e337`.

### 7.1 (b) Infinity rows (C = 0)

**What upstream does.** `EndpointQROM.normalizedEndpointWords` XORs `endpointTagMask` (bit 512 of columns 0, 3, 5, 6) with the row's `.infinity` constant. `normalizedEndpointWords_infinity` proves that **all eight normalized words are identically zero** when `constantPoint Q (coeffs row) = 0`. `normalizedEndpointWords_zero_action` and `batchUnitary_infinity` then get the identity from swaps with every pair equal to (0,0). For C ≠ 0, `normalizedEndpointWords_finite` shows the normalized words equal the raw `readEndpointWords`.

**Flag-only behaviour on such a row.** Every sₖ and tₖ equals 0. If acc = 0, all four flags fire. The update adds sₖ⊕tₖ = 0, so acc is unchanged. The clear test [acc = tₖ] equals the compute test [acc = sₖ], so every flag clears. On any other acc, no flag fires. So the result is the identity with clean flags, with no fix needed. The one change is that the "at most one flag" claim holds only for C ≠ 0. To keep the tag behaviour, reuse the same tag-flip leaf gates (`batchTags`, a `whenBit` on the row's `.infinity`) in every chained query.

**Reachability.** These rows are unreachable on valid branches when Q ≠ 0:
- `SharedTable.coefficientAt` rows are `leftCoefficients j a = coefficients (oddCoefficient j a) 0`, i.e. odd multiples of G, or `rightCoefficients`, i.e. odd multiples of Q.
- `BatchedWindowState.windowPoint_ne_zero (hQ) (hn : Q≠0)` uses `oddWindowPoint_ne_zero`.
- `batchedWindowSources_coherent` already eliminates the `zero` case with `False.elim`.
- `SignedBatchReady` carries `constantPoint … = .some hC` for the routed row.

### 7.2 (a) Validity

**The hypothesis upstream already has.** `BatchedWindowState.SignedBatchReady Q w s` is:
- `BatchedPointReady s`, and
- ∃ x y hC with `constantPoint Q (coefficientAt (batchWindowRows w (routeLabel …))) = .some hC`, and
- ∃ P with `pointStateCoordinates s = fig14EncodedEquiv x (±y) (fig14PointEncoding P)`.

After `windowYNegate` it becomes the data form used by `placedBatchState_finite`: `st ∘ accumulatorPort = coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P'))`. `signedBatchState_middle_ready` and `signedBatchState_pointWrite` derive it as `hd`, and `batchUnitary_finite` takes the same `hdata` form.

**How it reaches every executed branch.** `BatchedWindowCoherent.batchedWindow_coordinate_ready` proves `SignedBatchReady` for the output of the coordinate stage on every `BatchedWindowValid` input. `batchedWindowSources_coherent` / `batchedWindowCore_coherent` state the whole window as `CoherentlyImplementsOn … BatchedWindowValid`. `WindowValidity` (`batchedWindowValid_*`, `actualBatchedWindow_branch_supported`) carries that predicate across Fourier, address and window steps. So every basis state with nonzero amplitude entering the correction satisfies acc = F(P) for its row's C.

**What is missing.** Upstream proves the placed correction only on `BatchReady` (total: `placedBatchSource_state`) and composes it in `signedBatchSource_coherent` with a `batchedPointReady_batch` side condition. The new component needs a `CoherentlyImplementsOn` on the stronger predicate. That predicate is already in hand as `hd` inside `signedBatchSource_coherent` / `signedBatchState_middle_ready`, so the composition changes locally (S/M). Use `composeCoherent` and `restrictCoherent`. No new global invariant is needed.

### 7.3 (c) Distinctness

- **Missing.** The bench has no lemma for "2C ≠ 0 ∧ 3C ≠ 0".
- **Available.** It has `Math/BitcoinPrimes.order_prime : Nat.Prime order`, `Math/EllipticCurve/GeneratorOrder.{generator_order, generator_nsmul_eq_zero}` (which use Mathlib `addOrderOf_eq_prime`), and `Coefficients.coefficients_point` (C = a•G + b•Q, so order•C = 0 given hQ).
- **Proof (S).** C ≠ 0 and order•C = 0 give `addOrderOf C = order` via `addOrderOf_eq_prime`. Then k•C = 0 implies order ∣ k (`addOrderOf_dvd_of_nsmul_eq_zero`), which is impossible for k = 2, 3.
- **What it gives.** The inputs 0, C, −C, −2C are pairwise distinct. With F injective (`fig14EncodedEquiv` is an `Equiv`, and `fig14PointEncoding_injective`) and T injective (`add_right_cancel`), the s and t columns are each pairwise distinct. For non-exceptional P, F P = T P (`fig14EncodedEquiv_nonexceptional`, used in `fixedExceptionSwaps_correct`), so an unmatched acc never equals any tₖ.

### 7.4 Zero test with only 855 labels

**Live during the correction.**
- acc: 263–518, 580–835, 838 (513);
- address and sign bank (16);
- query control 836;
- path 519–533 (15). The path is clean between queries.

**Clean.** 0–262, 534–579 and 837, which is 310 labels (`docs/CONTRIBUTIONS-PLAN.md` §1). These are scratch that `windowYNegate` also borrows clean (`range' 7 256`, 558–561). Partial guess: that cleanliness lives in `PointLookupValid` / `Secp256k1ZeroAllowedInputValid`, which `BatchedPointReady` includes. Confirm the exact clean list when implementing.

**Test of f ^= [acc ⊕ col = 0].**
- X-conjugate all 513 acc bits.
- A = 257 acc bits: a clean Gidney AND chain gives 256 ANDs (255 temporaries plus anc). These are measured-erased top-down with CZ fixes (`EEA/MeasuredAnd.measuredAndErase_coherent_uncompute`).
- f ^= AND(B ∪ {anc}) over 257 controls with the dirty chain, 4·255 = 1,020 CCX.
  - Its donors are 255 of A's acc wires. They are disjoint from the controls B ∪ {anc} and the target f, and are restored.
  - Brief 09's `dirtySweep_run` / MCX lemma applies with `hca` (controls ≠ donors) and `ha` (donors injective).
- Cost: **1,276 CCX per test**. Clean labels used: 256 + 4 flags = **260 of 310**.
- Update queries use fₖ as the unary `control`. `tableAddressTree_layout` takes the control as a parameter, and a flag in 0–3 is disjoint from the index and path wires. `runLeafState` ANDs the control into the path, so the query is genuinely controlled.

**Exact window T.** 13 × 229,369 + 8 × 7 × 1,276 = **3,053,253**.

### 7.5 Records

**Per window.**
- 13 × 32,767 = 425,971 measurements from queries, plus 8 × 256 = 2,048 from AND erasures, for 428,019. That is −30,719 against 458,738.
- Every branch has the same count, which fits the fixed `Straight` count form.

**Per round.** 28 × (−30,719) from the windows, plus −3,076 because the reset list shrinks from `batchedResetWires` (3,931) to the 855-label core. That gives **−863,208**.

**Six rounds.** **5,158,465,644 < 47,471,340,504**. Stride, positions, decoder offsets and `UniformT` must be recomputed for the new counts.

### 7.6 Remaining work for the implementation brief

1. Flag model and chain-query XOR lemma, reusing `unaryAction_coherent`, `endpointSelectGates_source`, `tableXorGates`, and the tag gates.
2. Zero test from clean-AND plus the dirty chain.
3. Distinctness lemma (S).
4. Strengthen the predicate for `signedBatchSource_coherent` and prove correctness via `readEndpointWords_pairs` / `fixedMatching_comp`.
5. New window segments, reset list (855 labels), support (`CompleteSupport` = 855), counts, stride, positions, `UniformT`, slots and assembly.

The acceptance proof is unchanged.
