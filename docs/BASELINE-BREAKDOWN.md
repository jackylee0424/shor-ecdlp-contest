# Shipped entrant resource breakdown

Audited 2026-10-29 against bench HEAD `535a493` at `/home/gitzard/shorecdlp`. The bench was read only. These are source-derived formulas, not a fresh official score or kernel replay. The shipped entry declares **206,642 qubits, 355,060,161,799,520 T-model and 530 measurements**, with a complete protected `Certificate officialLimits layout entry bounds` in [Entrant/Main.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Entrant/Main.lean). Its Q×T is **73,370,341,954,576,411,840**.

Run the dependency-free calculator from the lab:

```sh
python3 workspace/baseline_breakdown.py
# 206642
# 355060161799520
python3 workspace/baseline_breakdown.py --details
```

The script derives both declared totals from subroutine formulas and asserts the independently stated intermediate Lean counts. It also cross-checks the distinct 26-trial Naive numeric certificate. No Lean elaboration was needed for this audit.

## Which circuit is shipped

[Entrant/Trial.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Entrant/Trial.lean), `trialGatesE`, reuses Naive field/point arithmetic and its workspace. Each phase register adds nine high bits to the original 256 bits. One trial prepares 530 Hadamards, performs **265 controlled constant-point additions for G and 265 for Q**, applies two 265-bit inverse QFTs, and observes the two phase registers. There is no outer reset/repetition suffix. `coeffE`/`tableE` contain 530 fixed coefficient rows; precomputed points are supplied through the protected evaluator, so there is no quantum point-doubling loop to build the tables.

`Success.success_of_window_mass` and `WindowMass.window_mass` support ≥99% success using a ≥199/200 window-mass estimate. The final proof is `Main.entryE_success`. This is distinct from the original 26-trial, 256-bit protected Naive entry (`Naive/Challenge/NumericCertificate.lean`). Historical PLAN figures describe earlier arithmetic and must not be used for this entrant.

## T-model formulas, from gates to scalar multiplication

Set `n = 257` (field arithmetic includes one headroom bit), `w = 513` (finite tag plus two 256-bit coordinates), and `m = 265` (phase precision). CCX costs 7; each primitive P costs 1; X/H/CX and measurement/reset cost zero. Reversing a classical arithmetic circuit preserves T count. All formulas below count executed gate lists, including their explicit compute/uncompute repetitions.

| Subroutine | Formula | T-model | Source definition / count lemma |
|---|---|---:|---|
| One-bit full adder | `3·7` | 21 | `Arithmetic/Adder.fullAdder_tCount` |
| Out-of-place ripple adder | `21n` | 5,397 | `Arithmetic/RippleAdder.ripple_tCount` |
| Modular add/sub forward compute | `2·21n` | 10,794 | `ModAdd.modAddCompute_tCount`, `ModSub.modSubCompute_tCount` |
| Clean modular add/sub | `2·42n + 7n = 91n` | 23,387 | `ModAdd.modAdd_tCount`, `ModSub.modSub_tCount` |
| In-place Cuccaro add/sub | `14n` | 3,598 | `InPlaceAdder.inPlaceAddCarry_tCount`, `InPlaceModular.inPlaceSubCarry_tCount` |
| Reduction with flag | `14n + 2·7n + 14n = 42n` | 10,794 | `InPlaceModular.reduceWithFlag_tCount` |
| Modular doubling | shift is free, then `42n` reduction | 10,794 | `InPlaceModular.modularDouble_tCount` |
| Controlled modular add | `112n` | 28,784 | `InPlaceModular.controlledModAdd_tCount` |
| Low-space Horner multiplication `M₀` | `n·(42n+112n) = 154n²` | 10,171,546 | `LowSpaceModMul.horner_tCount`, `program_tCount`; `Secp256k1Instance.mulCost` |
| Modular exponentiation `E₀` | `2·((2n−1)·M₀ + 7n²)` | 10,436,930,882 | `Secp256k1Instance.secpCost`, `secpProgram_tCount` |
| Field add/sub wrapper `A` | `2·91n` | 46,774 | `PointAdd.fieldAdd_tCount`, `fieldSub_tCount`, `fieldSubConst_tCount` |
| Field multiplication wrapper `M` | `2·M₀` | 20,343,092 | `PointAdd.fieldMul_tCount` |
| Field inversion wrapper `I` | `2·E₀` | 20,873,861,764 | `PointAdd.fieldInv_tCount` |

Here `Arithmetic/*` refers to [Naive/Arithmetic](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Arithmetic/README.md). The `PointAdd` count lemmas for field wrappers and individual branches are **private**: they explain the formulas but cannot be imported by their short names. Public endpoints include `pointAddFiniteCompute_tCount`, `pointAdd_finite_tCount` and `controlledPointAdd_tCount_of_ne_zero`.

The modular add/sub computation uses two ripples to form a raw answer and correction candidate, selects a word with `n` CCX gates, then reverses the computation. The multiplier uses an MSB-first Horner recurrence with reused mask/modulus/three flags, not the older history-based multiplier in `ModMul.lean`. See [LowSpaceModMul.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Arithmetic/LowSpaceModMul.lean) and [Secp256k1Instance.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Arithmetic/Secp256k1Instance.lean).

Fermat inversion uses the **generic reversible exponentiation schedule** loaded with exponent `p−2`; it is not specialized to that constant's Hamming weight. The schedule performs `2n−1 = 513` multiplication calls in its forward computation, word-selection cost `7n²`, and reverses the whole computation. The field wrapper separately runs and reverses this complete engine to copy out a clean result. This accounts for both factors of two. `secp_fermat_inverse` specializes the correctness theorem to that same circuit.

### Affine branches and controls

The following formulas come directly from [PointAdd.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Arithmetic/PointAdd.lean), including the `.reverse` segments in `genericPointCompute`, `threeXSquared`, `doublePointCompute`, and the three branch constructors. Let `S = 7w = 3,591` be one controlled point-word copy/selection.

| Subroutine | Formula | T-model |
|---|---|---:|
| Generic affine coordinate computation `G` | `9A + 4M + 2I` | 41,829,516,862 |
| Clean `3x²` computation `X₃` | `3A + 2M` | 40,826,506 |
| Doubling coordinate computation `D` | `2X₃ + 7A + 4M + 2I = 13A + 8M + 2I` | 41,911,076,326 |
| Point flags/setup `F` | `2·14·255 + 3·7` | 7,161 |
| Generic branch | `2G + S` | 83,659,037,315 |
| Doubling branch | `2D + S` | 83,822,156,243 |
| Infinity-input branch | `S` | 3,591 |
| Finite-constant point computation `C` | `F + 2G + 2D + 3S` | 167,481,204,310 |
| Uncontrolled out-of-place point add | `2C` | 334,962,408,620 |
| Controlled out-of-place point add | `2(C + S)` | 334,962,415,802 |
| Controlled in-place point add `P` | `4(C + S)` | **669,924,831,604** |

Flags include two 256-bit equality tests and three Toffolis; the one-bit infinity test is Clifford-only. Both the generic and doubling arithmetic circuits execute before their outputs are selected. A false quantum branch/control does not skip these gates. Thus doubling is paid inside every finite-constant controlled addition, even though there is no separate scalar-accumulator doubling loop.

[Controlled_PointAdd.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Arithmetic/Controlled_PointAdd.lean), `controlledPointAddOut`, computes/selects/copies/uncomputes. `controlledPointAdd` calls that for C, swaps the point register with its temporary output, then reverses the corresponding operation for −C. The swap is three CX per bit and contributes zero T. `controlledPointAdd_tCount_of_ne_zero` gives the exact `P`; addition by the zero constant has zero T (`controlledPointAdd_zero_tCount`).

### Outer total and independent attribution

[ScalarMul.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Arithmetic/ScalarMul.lean), `scalarMulCore` and `scalarMulWork`, reuse one controlled-point workspace for every bit. [NumericCosts.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Challenge/NumericCosts.lean), `controlledPoint_templateT` and `scalarGates_templateT`, count the fixed template at `P` per populated scalar step.

[QFT/Proofs/Count.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/QFT/Proofs/Count.lean), `tCount_iqft`, gives `15·m(m−1)/2 = 524,700` per axis. The clean-ancilla controlled phase has two CCX and one P, hence 15 T; bit reversal/Hadamards are free.

```text
one scalar axis = 265 × 669,924,831,604 = 177,530,080,375,060
both axes       = 530 × 669,924,831,604 = 355,060,160,750,120
two inverse QFT = 2 × 524,700          =               1,049,400
TOTAL T-MODEL                          = 355,060,161,799,520
```

This is exactly `Entrant.templateT_trialE` and `straightT_entryE`. `entryE_tModel` proves a uniform upper bound for all Q using `straight_t_bound`; inactive constant-guarded slots are still charged statically. On the intended nonzero subgroup inputs every power-of-G/Q addend is finite, so the source formulas explain the full finite-template cost. The certificate itself asserts an inequality, not equality of instantiated resources for every public input (for example Q=0 disables its additions).

Expanding `P = 176A + 96M + 32I + 4F + 16S` provides a non-overlapping attribution of the whole declared T total:

| Category | Whole-entry T | Share |
|---|---:|---:|
| Field inversion wrappers (16,960 calls, including reversals) | 354,020,695,517,440 | 99.70724% |
| Other field multiplication wrappers (50,880 calls) | 1,035,056,520,960 | 0.29152% |
| Field addition/subtraction wrappers (93,280 calls) | 4,363,078,720 | 0.00123% |
| Point flags/setup | 15,181,320 | <0.00001% |
| Point copies/selections | 30,451,680 | <0.00001% |
| Two inverse QFTs | 1,049,400 | <0.000001% |

The field inversion bucket includes all exponentiation multiplications/selects; the “other multiplication” bucket excludes them. Nested rows in the earlier subroutine tables must not be summed independently.

## Qubits: reused subroutine space and the declared envelope

Qubits count distinct physical labels across the program. Calls and branches reuse scratch; neither multiplication counts nor 530 scalar steps multiply the wire footprint. The original layout in [Correctness/EndToEnd.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/Naive/Correctness/EndToEnd.lean) defines A at 0–255, B at 256–511, the point at 512–1024, QFT ancilla 1025 and workspace start 1026. Entrant appends wires 206624–206632 and 206633–206641 for its extra phase bits.

| Disjoint allocation component | Formula | Declared-envelope wires |
|---|---|---:|
| Both phase registers | `2·265` | 530 |
| Accumulator point | `1 + 256 + 256` | 513 |
| Shared QFT ancilla | `1` | 1 |
| In-place point temporary + controlled-output choice | `2·513` | 1,026 |
| Point-local reusable field registers X/Y/T0…T4 | `7·257` | 1,799 |
| Point predicate constant/difference/history area | `256 + 1 + 4·256` | 1,281 |
| Point branch flags | `6` | 6 |
| Candidate and selected point words | `2·513` | 1,026 |
| Shared arithmetic-engine dense envelope | `780·257` | 200,460 |
| **Total** | | **206,642** |

The four point-local rows sum to **4,112** (`PointAdd.localWorkSize_eq`, private). Controlled-point temporary and choice occupy 1026–2051; point-local workspace is 2052–6163; the engine starts at **6164**. `pointAddArithmeticWork` is the deduplicated union of shifted add/mul/exponentiation layouts, all with that same engine offset. This is why space is shared between addition, multiplication, inversion, generic addition and doubling.

Useful isolated layout sizes, **not extra additive allocations**:

| Arithmetic subroutine | Public/clean output ports | Scratch | Layout total |
|---|---:|---:|---:|
| Width-257 clean modular adder | `3n = 771` | `5n+2 = 1,287` | `8n+2 = 2,058` |
| Width-257 Horner multiplier | `3n = 771` | `2n+3 = 517` | `5n+3 = 1,288` |
| Fermat/exponentiation engine | `3n = 771` | `774n+3 = 198,921` | `777n+3 = 199,692` |

The multiplier's public theorem is `secpMulLayout_allWires_length`, with `secpMulProgram_qubitCount ≤ 1288`. `LowSpaceModMul.work_length` and `layout_allWires_length` expose the generic formulas. The adder follows `addScratchBlocks`/`secpAddLayout`. The exponentiation size follows `secpLayoutBlocks` and `secpPlan_allWires`, with disjointness from `secpLayoutBlocks_ids_nodup`.

### Why 206,642 is an upper bound, not an exact distinct-wire count

`Secp256k1Instance.historyCount_eq` proves **770** stored intermediate width-257 registers (`historyCount n = 3n−1` for n>0): **197,890 wires**, almost all the allocation. The exponentiator has full register IDs 0–776: base/exponent/output/initial accumulator, 770 history registers, a duplicate register, then modulus and mask. It has only **one bit each** at register IDs 777, 778 and 779. Thus its sparse layout has `777·257 + 3 = 199,692` labels, while the inherited proof encloses it in `range (780·257)`, charging **768 unused high positions** of those last three blocks.

The proof of the original dense capacity is `bitcoinDeclaredWires_subset`/`bitcoinECDLPTrial_fixed_support`; its internal `pointAddArithmeticWork_upper` rounds all three engine layouts to that same 780-block envelope. Entrant's `support_sub`, `entryE_support` and `entryE_qubits` retain it and add the 18 phase bits. The add/mul layouts fit within the exponentiator's full initial blocks, so they do not fill those sparse holes.

Consequently **205,874 = 206,642−768 is a source-derived upper bound from the named sparse layouts**, reproduced by the calculator. It is not a new kernel-checked certificate, nor a claim that every remaining support label occurs in the gate list. The submitted score still uses the declared 206,642 until a new resource proof/bound is made. This is a straightforward ≈0.37% space opportunity; the dominant optimization opportunity remains inversion and its stored history.

## Measurements and admission quantities

`entryE_measurements` proves exactly **530** observations. The Naive arithmetic and coherent QFT used here have no internal measurements; readout emits one record per phase bit. `tableE_length` proves **530 coefficient rows**. `entryE_gateSlots` proves a conservative **144,200,000,001,060** syntax-slot cap, below the 4·10^15 limit. The nearestPair decoder has one trial/candidate; the certificate discharges its budget separately. The T figure is not a gate-slot count.

## 2607_13816 status: legacy streaming is proved; protected migration remains open

The authoritative distinction is between the paper implementation's **Q-dependent adaptive circuit family** and the challenge's **fixed Q-independent coefficient/straight-line entry**. [INTEGRATION.md](/home/gitzard/shorecdlp/ShorECDLP/Submission/2607_13816/INTEGRATION.md) and [Submission.lean](/home/gitzard/shorecdlp/ShorECDLP/Submission/2607_13816/Submission.lean) report completed legacy contracts. [STREAMING_CERTIFICATE_HANDOFF.md](/home/gitzard/shorecdlp/docs/STREAMING_CERTIFICATE_HANDOFF.md) explicitly says the migrated producer is unfinished. Early PLAN phase-status paragraphs are historical; they must not erase subsequently completed streaming sampling/repetition proofs.

### Already proved for the legacy implementation

- Pure EEA model, exact rational termination/horizon argument (1,620 microsteps), corrected active windows and physical forward/reverse schedules. `EEA/Bounds.lean`, `Windows.lean`, `MeasuredSchedule.lean` and `MeasuredWrapper.lean` connect measured execution coherently to inversion; these are not pending Fermat-to-EEA replacements.
- Measured in-place division/multiplication with exchanged data banks and phase correction (`Arithmetic/InPlace.lean`, `SourceInPlace.lean`); total controlled affine addition including finite exceptional repair (`PointTotal.lean`, `PointTotalCircuit.lean`). Generic raw calls retain explicit valid-input/nonzero-domain conditions.
- Signed-window/QROM arithmetic, direct first lookup and 28 raw additions (15 remaining left, 13 right); 256/208-bit Fourier histories; physical relocation to a single reused 16-wire address bank. The streaming proof preserves full branch histories and clean-bank premises (`RawStream`, `RawBankReuse`, `TwoAxisReuse`, `StreamKernel`).
- Excluded preparation mass ≤7/4096, good-input arithmetic, actual chronological record parsing, and interference comparison ≥9/16 of the ideal selected-event mass minus 147/16384. `StreamSamplingSuccess` establishes **≥8% actual single-trial public-decoder acceptance**, normalized total mass and accepted-scalar correctness. Bad-input mass is not simply declared to be output failure probability.
- Actual reset/repetition and **≥99% success in 56 trials**, with branchwise return to zero (`StreamResetRepetition`). This is a proved sequential-instrument statement, not assumed independent classical retries.
- Primitive gate counts on the same actual streaming program (`StreamGateCounts`), and removal of unused wire 837 (`StreamTightSupport`). `Submission.Streaming.tight_certificate` combines the following bounds with success and soundness:

| Metric | One streaming trial / 56 trials |
|---|---|
| Distinct wires | ≤854 for both (earlier joint contracts use ≤855) |
| Trial measurements | exactly 847,701,655 |
| Repeated measurements including reset | ≤47,471,340,504 |
| Toffolis | 2,040,822,631 / 114,286,067,336 |
| Dyadic phase operations | ≤54,168 / ≤3,033,408 |
| Abstract T-model | ≤14,285,812,585 / ≤800,005,504,760 |

The tight support is `range 837 ++ [838] ++ range′ 855 16`, cardinality 854; the largest label is 870. The repeated bound is `56·(847,701,655+854)`. The abstract T bound is `7·114,286,067,336 + 3,033,408`. These are proved legacy bounds, not just paper estimates. Their product would be 683,204,701,065,040, **but this is not an admitted challenge score**. The separate older raw program has ≤1,303 wires, and a separate corrected 26-round contract also exists.

### Protected migration: completed pieces and missing closure

The fixed syntax cannot submit arbitrary Q-dependent endpoint matching or callbacks. A new fixed-shape exceptional correction is therefore being built under `2607_13816/Challenge/`:

| Layer | Evidence already present | Remaining obligation |
|---|---|---|
| Protected compilers | Arithmetic/EEA/lookup/Fourier modules prove ordered-instrument equality and local T agreement | Aggregate physical validity/support/cost for all actual composed windows |
| Shared constant table | `SharedTable`/`OddFields` provide the 983,040-row table and reference adapters | Preserve selected-row consistency/readiness through the complete signed window |
| Five-word correction | `BatchExecution.batchUnitary_schedule`, `BatchCoherent.batchSource_coherent`, `BatchFrame.batchUnitary_fullFrame`, `BatchTemplate.placedBatchProgram_wellFormed` | Compose with preceding/following coordinate and sign stages under actual entry invariants |
| Physical point encoding | `AccumulatorEncoding.placedBatchState_pointWrite`; `WindowNegation.windowYNegateState_pointWrite`; `CoordinateConjugacy.signedCorrection_negY` | Whole signed point-add correctness, canonical output and all work restored before the next window |
| Actual outer program | `WindowBody.batchedOuterPlan`: direct first lookup plus 28 corrected additions; 3,931-wire reset list | Reset/cleanliness proof for this actual new program, plus whole-trial sampling/retry theorem |
| Record binding | `OuterPlan.entry_records`, `entry_reads`, `layout_trial` derive actual 256/208-bit Fourier positions; stride uses real body counts | Connect these actual reads to the protected verifiedCandidate ≥99% event for the new window implementation |
| Budgets/assembly | `OuterBudget` derives uniform resource inequalities; `StreamingAssembly.certificate` assembles a certificate from explicit producer proofs | Instantiate numerical bounds, syntax-slot/record/table admission proofs and the producer record |

[STREAMING_BATCHED_WINDOWS.md](/home/gitzard/shorecdlp/docs/STREAMING_BATCHED_WINDOWS.md) gives exact component costs: fourteen 15-bit unary queries and sixteen transpositions per correction, **3,784,382 T and 458,738 measurements**. Its 3,932-wire component support estimate is analytical and excludes whole-program obligations. The previous eight-resident-word variant uses 5,471 estimated wires, 1,031,954 T and 65,534 records per correction. The five-word version trades 1,539 wires for extra T/measurements. Across 56·28 corrections its correction-only T is 5,933,910,976; this cannot be added to the legacy total and presented as a certified new total.

[STREAMING_OUTER_RESOURCES.md](/home/gitzard/shorecdlp/docs/STREAMING_OUTER_RESOURCES.md) provides conservative uniform-window formulas:

```text
slots        ≤ 56·(29S + 54,634)
T-model      ≤ 56·(29T + 54,168)
measurements ≤ 56·(29M + 464 + reset.length)
qubits       ≤ commonSupport.card
```

Actual measurement count is `56·p.stride`, from the sum of the actual body counts, Fourier records and reset records. The uniform-window bound may be too loose for admission. The organizer measurement cap is already equal to the legacy tight repeated upper bound; additional fixed correction queries/reset support have no automatic headroom. Even the correction-only difference from the eight-word variant is `56·28·(458738−65534) = 616,543,872` records. A new complete accounting and likely a measurement-saving tradeoff are required; execution equality by itself cannot transfer the legacy budgets.

The planned final producer file **`Challenge/StreamingCertificate.lean` is absent**. No `streamingEntry`/`streamingBounds`/`streamingCertificate` producer exports currently close the protected contract. `CertificateAssembly.lean` has explicit success/resource/well-formedness premises, not a hidden completed instance. The organizer `scripts/challenge/streaming_acceptance.py` is an adapter to run after that producer exists; its Naive self-test would not establish streaming acceptance.

### Rough remaining size and separate targets

This is a substantial multi-module integration task, not an unfinished arithmetic library and not a final record constructor alone. A practical work split is **five proof packages**: (1) signed-window readiness/row consistency and total point action, (2) complete physical validity/frame/scratch restoration, (3) actual-program shared support/T/slots/record accounting with a feasible measurement budget, (4) replacement of the legacy sampling/reset/retry chain by this composed implementation and its protected decoder, and (5) final producer exports plus protected-judge/kernel replay. Existing generic `OuterPlan`, coherent-refinement and compiler lemmas reduce duplication, but local correctness of adjacent stages does not establish their premises at composition boundaries.

Planning estimate: several person-weeks of Lean integration and resource optimization, with the measurement-budget repair the main uncertainty. This is an engineering estimate from the missing theorem families, not a measured delivery forecast. A smaller first milestone is one complete signed window with a full canonical point/frame theorem; numerical admission should be calculated before propagating it to all 56 rounds.

The paper's **835-wire** whole-algorithm target, tighter success analysis, phase-rotation synthesis/error budgets and an efficient executable classical decoder are separate work. [REFERENCE.md](/home/gitzard/shorecdlp/ShorECDLP/Submission/2607_13816/REFERENCE.md) pins the paper/generator, quarantines its conflicting Toffoli estimates and 835-wire complete-schedule claim, and explains the one-extra-lower-lane active-window correction. Those historical warnings do not negate the later 854-wire legacy theorem. Phase synthesis and decoder efficiency are useful deployment goals; the present challenge uses an abstract P cost and a protected mathematical decoder, so they are not additional admission requirements here.
