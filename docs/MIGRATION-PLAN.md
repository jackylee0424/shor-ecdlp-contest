# Completing 2607_13816 → Straight inside Entrant

Audited 2026-10-29, bench `535a493f520dd7efe8c1cfc0b8b5a2741d5b35c1`.
`B/` below means `~/shorecdlp/ShorECDLP/Submission/2607_13816/`.
All implementation goes in `Submission/Entrant/Streaming/`; the protected sources are imports.
S = local lemma; M = connected lemmas, plausibly one session; L = several substantial modules;
XL = a major semantic/probabilistic bridge. These are effort estimates, not promises.

The existing `batchedOuterPlan` is **over the measurement limit**. Its source-formula support is
3,932 wires, including zero flag 837, rather than the reset-list length 3,931 or the legacy 854.
The proposed repaired construction has an analytical target of **3,932 Q, T ≤ 810,996,871,160,
Q×T ≤ 3,188,839,697,401,120**. This is conditional on the milestones below, not an accepted score.
`Entrant/Main.lean` continues to export the certified baseline; no scoring or submission was done.

## 1. Assembly obligation inventory

The five fields of `ChallengeMigration.StreamingAssembly` and the four arguments added by its
`certificate` theorem are the complete top-level obligation list. No concrete instance for the
batched producer exists in the protected sources.

| Field / argument | Existing evidence | Still required for an actual entry | Size |
|---|---|---|---|
| `kind` | `OuterPlan.layout`, `OuterPlan.assembly`: wrapped shift by construction | Select the actual plan's layout | S |
| `precision` | Same definitions use `legacyDecoderParams = (256,208)` | Use those params; retain Fourier bit order | S |
| `wellFormed` | `OuterPlan.repeat_wellFormed`, `round_wellFormed`, `outerAxis_wellFormed` | Instantiate `p.WindowsWellFormed` for first and all 28 odd windows | L |
| `resources` | `OuterBudget.resources` composes local budgets for every Q | Actual producer support / slots / counts / T, including correction and reset changes; see all budget fields below | L |
| `success` | `actualBatchedWindow_run` is instrument equality to its source; legacy `streamRepeatedProgram_tight_certificate` proves ≥99% for another program/event | Coherent all-input window action, outer Fourier law, decoder-event equivalence, reset/repetition independence | XL |
| `hg` gate slots | `OuterBudget.gateSlots`, `OuterPlan.repeat_slots_le` | Bound actual syntax including disabled optional slots; numeric screen is comfortably under cap, but local theorem missing | M/L |
| `hm` final cursor | `OuterBudget.finalCursor`, `OuterPlan.stride_le`; exact indices in `OuterPlan.stride` | Repair overflow and prove counts; use a weighted first-plus-28 estimate to avoid uniform-window overcount | M/L |
| `ht` table rows | `coefficientTable_length = 983040` | Cast the plan to that length and prove `coefficientTable.get` equals `coefficientAt`; official cap is exact | S |
| `hc` candidate limit | `streaming_candidate_budget`, `OuterPlan.candidate_budget`; `budget55 = 56*(2^49+2)` | Specialize to `officialLimits`; no arithmetic/search redesign needed | S |

`StreamingAssembly.resources` concerns **all curve points Q**, including zero; a success proof only
concerns `Q ≠ 0` with `Q=d•G`. The window compiler's run/T theorems take `hQ : order • Q = 0`.
For success this follows by commuting scalar multiplication with `order • G = 0`. For resource
proofs either discharge it for every curve point using an existing curve-order result, or avoid it
by proving table-value-independent resource bounds for arbitrary constant readers. Do not assume
that the success hypothesis supplies the resource field's universal quantifier.

### Every field of `OuterBudget`

| Field | Existing theorem / definition | Missing specialization | Size |
|---|---|---|---|
| `support` | `batchedResetWires`; `signedLookupCoordinateProgram_wires`; placement bounds | Use reset list plus `[837]` as support, cardinal 3932; support remains large after reset pruning | M |
| `slotBound` | `registerCorrectionProgram_slots`, `deferredCorrectionProgram_slots`, `literalProgram_slots` | Compose actual measured arithmetic + QROM slot formulas | L |
| `tBound` | `coordinateProgram_tCount`, `sharedCoordinateProgram_tCount`, `placedBatchSource_tCount` | Actual compiled-window numeric estimate; M1 supplies the correction/compiler bridge and coordinate totals | M |
| `measurementBound` | `placedBatchProgram_count = 458738`, `Straight.measurementCount` | Exact coordinate/sign counts and new query compiler counts; current odd window is 30733484 | M |
| `fourierSupport` | Standard plan uses reversed `range' 855 16` | List inclusion in 3932-wire support | S |
| `resetSupport` | Supplied reset list | Include the selected reset list in support | S |
| `controlSupport` | Control label 836 | Membership | S |
| `windowSlots` | Generic append/reindex/shift slot equalities | Bounds for first lookup and actual odd bodies, uniformly over cursor | L |
| `windowCount` | First count 65535; `placedBatchProgram_count` | Count composition for full body, including signs and changed erasures | M |
| `windowT` | Compiler/source correspondences for nearly all arithmetic | Instantiate at actual rows/cursors/histories and compose; repaired body needs its new theorem | M/L |
| `windowSupport` | Legacy support theorems plus relabel machinery | Source support does not follow from equality of `.run`; prove syntactic support for the compiled body, including optional gates | L |

**The generic budget is too loose at the exact cap.** `OuterBudget.bounds` uses 29 times the largest
window count, charging the first window like an arithmetic window. Keep its composition lemmas,
but add heterogeneous sums (one lookup + 28 odd bodies), or call `OuterPlan.assembly` with independently
proved bounds. Even a repaired producer can fail `recordBudget` if this uniform estimate is used.

### Producer-facing dependencies and residual hypotheses

This table expands the obligations hidden behind the rows above. A source run theorem establishes
execution, not automatically static support, optional-slot physical validity, or decoder success.

| Component | What already exists (actual theorem names) | Hypotheses still to instantiate / missing glue | Size |
|---|---|---|---|
| Shared table / coefficient mapping | `coefficientAt_first`, `_left`, `_right`, `_window`; `sharedCoordinateProgram_run`, `_tCount`; `sharedFirstWindowProgram_instantiate` | Finite-table get adapter; `order•Q=0`; distinguish first **lookup** count 65535 from `sharedFirstWindowProgram` count 65551 (includes Fourier) | S/M |
| First window | `actualFirstWindow_run`, `firstLookupProgram_run`, `_tCount`, `pointRefs_read` | Coherent lookup on prepared bank / zero accumulator, clean path/frame, physical validity, support and slots | M |
| Coordinate core | `coordinateSources_eq`, `coordinateProgram_run`, `_tCount`, `signedLookupCoordinateProgram_coherent` | Satisfy `PointLookupValid`: clean arithmetic scratch, zero flag 837, canonical x/y, control 836=true; derive raw encoded permutation with full frame and sign convention | L |
| Zero-allowed field arithmetic | `zeroDivisionProgram_run`, `_tCount`, `zeroMultiplicationProgram_run`, `_tCount`; `secp256k1ZeroAllowedDivision_certificate`, `secp256k1ZeroAllowedMultiplication_certificate` | Canonical domains and flag cleanliness between stages; no nonzero-denominator assumption may remain for exceptional inputs | M |
| In-place arithmetic | `divisionProgram_run`, `_tCount`, `multiplicationProgram_run`, `_tCount`, `multiplicationAfterResetProgram_tCount` | Fixed target/dirty bank lengths and layout; retain all prior reset records through reverse EEA and cleanup; physical/support/slot and exact-count compiler lemmas still needed | L |
| EEA measured step/schedule/wrappers | `measuredStepProgram_run`, `_tCount`; `measuredInverseStepProgram_run`, `_tCount`; `measuredEEAForwardProgram_tCount`, `measuredEEAReverseProgram_run`, `_tCount`; `measuredForwardWrapperProgram_run`, `measuredReverseWrapperProgram_run`; `measuredForwardDataBankProgram_run`, `measuredReverseDataBankProgram_run` | Forward/reverse packed-bank invariants, valid metadata, scratch separation already handled in source semantics; migrate physical/size/support estimates to the compiler and its relabeled banks | L |
| Gidney add / compare | `gidneyProgram_run`, `_tCount`, `_records`; `compareGEProgram_constant_run`, `uncontrolledCompareProgram_tCount` | Width relations (`input.length = dirty.length+1`, matching constant length), concrete distinct wires, constants' zero shortcuts; run/T exist, full actual `WellFormed`/support/static-slot chain does not | M/L |
| Remaining arithmetic compilers | Horner, Square, ModularAdd/Negate, Phase, LengthRefresh, RangeScan, Interval/IntervalWhole, VChain, ZeroLeaf/ZeroMap all export `_run` / `_tCount` | Close concrete physical geometries and fixed counts using the actual (possibly relabeled) bank allocation; do not rebuild their arithmetic semantics | L combined |
| Register corrections | `registerCorrectionProgram_run`, `_slots`, `_tCount`; `deferredCorrectionProgram_run`, `_records`, `_slots`, `_tCount`; `appendRetaining_run`, `_tCount` | Match target/record lengths (compiler truncates to `min`); bind indices to the right chronological reset/carry records; well-formed H/X/H or H/CX/H gates; T contribution is zero, slots are not | M |
| Batched correction query | `batchQuery_coherent`, `batchSelection_nodup`, `batchWindowTree_layout`, `batchWindowTree_below` | Query conditions: clean paths, distinct selected ports, decoder/endpoint separation. Current concrete geometry helpers exist; instantiate in compiler physical/support proofs | M |
| Batch schedule / swap geometry | `batchSchedule_valid`, `batchSwap_geometry`, `batchOpCircuit_model`, `batchSource_coherent`, `batchUnitary_schedule`, `_finite`, `_infinity`, `batchUnitary_fullFrame` | `BatchReady`: clean paths and comparator scratch, flag=false, control=true; all five endpoint words initially zero; select finite/infinity case; preserve these across all windows | M/L |
| Placement / correction result | `placedBatchSource_state`, `placedBatchState_finite`, `placedBatchState_pointWrite`, `_coordinates`, `_ready`, `_frame` | Supply `hs`, `hz`, `hv`, finite selected row `hr`, encoded-coordinate result `hdata`; lift infinity case to the same full-state interface; relate routeLabel to actual address and shared row | M/L |
| Sign conjugacy | `fig14CoordinateEquiv_negY`, `fig14EncodedEquiv_negY`, `signedCorrection_negY`, `windowYNegate_coherent`, `windowYNegateState_pointWrite`, `_ready` | Compose both sign branches into signed group addition; cancel adjacent identical negations on the valid subspace | M/L |
| Physical lowering | `lookupProgram_wellFormed`, `unaryLookupOps_physical`, `ordinaryOp_physical`, `endpointTransposition_wellFormed`, `matchingCircuit_wellFormed`, `shiftStraight_wellFormed` | These are conditional helpers, not `batchedOuterPlan.WindowsWellFormed`. Prove arithmetic validity, batch leaf/control-target distinction, transport through coefficient reindex and wire permutation | L |
| Closed/relabelled windows | `closedWindow_run`, `shiftStraight_instantiate`, `_gateSlots`, `_wellFormed`; `relabelCompiled_run`, `_tCount`; `reindexStraight_instantiate`, `_gateSlots` | Explicitly transport WF/support/slots/T through final address permutation 839–854 ↔ 855–870. Avoid normalizing gigantic producer terms | M |
| Whole outer program | `actualBatchedWindow_run`, `actualFirstWindow_run`, `outerAxis_records`, `OuterPlan.entry_records`, `entry_history_length`, `entry_reads`, `layout_trial` | Local record membership already proved. Still identify **values/order** with the mathematical sampling words, coherent accumulator update under H, Fourier feedback prior bank order, and first-window offset | L |
| Resets / independent rounds | `resetProgram_run`, `resetProgram_wellFormed`, `reset_supported_program_zero`; legacy `streamRepeatedCandidate_success` | Current reset list omits 837; show it is already clean. For pruned endpoint resets use full frame + endpoint cleanup, prove whole supported state resets to zero and records do not affect later local programs | M/L |
| Sampling and decoder event | `streamRawDecoder_success`, `streamRawPublicDecode_success` (2/25); legacy `streamRepeatedProgram_tight_certificate` | New producer is totalized/corrected and has different histories. Prove its marginal Fourier distribution/event, connect protected `readWord` LSB convention to wrapped-shift decoder, protected verification/soundness, total branch mass, 56-fold failure product | XL |

The old `Positions.fourierPosition` and `legacyTrialStride` are **not** correct positions for the
current batched producer. Use `OuterPlan.positions`, automatically derived from actual counts.
`entry_reads` proves the words exist; it does not prove they have the required success distribution.
Removing measurements changes branch histories, so do not claim instrument-list equality to the
legacy program after cancellation/coherent erasure. Use coherent refinement / marginal event mass.

## 2. Source-derived costs and limits

Reproduce with `python3 workspace/streaming_costs.py` (also supports `--json`).
The calculator cites formulas in comments and asserts the legacy reference and intermediate totals.

| Component | T model | Measurements | Source |
|---|---:|---:|---|
| Legacy raw odd call | 510189274 | 30272702 | `Window/RawCounts.preparedRawProgram_counts` |
| Current totalized coordinate core | 510203526 | 30272702 | `Window/LookupPrimitiveCounts.signedCoordinatePrimitives` |
| Each extra Y negation | 21434 | 1022 | `negative_point_primitive`, `controlledModularNegate256_counts` |
| Placed batch, 14 queries / 16 swaps | 3784382 | 458738 | `BatchCost.placedBatchSource_tCount`, `BatchPlacement.placedBatchProgram_count` |
| Current odd window | 514030776 | 30733484 | Coordinate + two negations + correction |
| First lookup | 458745 | 65535 | `PointTable.firstLookupProgram_tCount`, first `OuterWindow.count` |
| Both Fourier axes / trial | ≤54168 | 464 | `OuterResources.outer_feedback_overhead`, 29×16 |
| Reset / trial | 0 | 3931 | `WindowBody.batchedResetWires_length` |

The zero wrappers cost **14252 T per odd window**, absent from the raw legacy core; they add no
measurements. The 28 arithmetic windows are not 29: the first window is a direct lookup.

```
T ≤ 56 * (458745 + 28*514030776 + 54168) = 806028979896
M = 56 * (65535 + 28*30733484 + 464 + 3931) = 48194018992
M - cap = 722678488 = 56*(28*(458738+2044) + 3077)
```

The support union is `[0,838) ∪ {838} ∪ [855,871) ∪ [1024,3589) ∪ [4102,4614)` in
half-open notation (the first interval includes 837). Cardinal **3932**; maximum label 4613.
Every reset label is used irrespective of Q; zero-test circuits also touch 837. Endpoint data word
5 has been exchanged with the low accumulator and **3589–4101 are not extra live ports**.
A bound using `range 4614` overcharges 682 holes. Merely counting reset entries undercharges 837.

| Limit | Current / proposed accounting | Result |
|---|---|---|
| Measurements 47471340504 | Current 48194018992 | FAIL; cannot fix by deleting 3077 extra resets alone |
| Rows 983040 | 65536 + 28*32768 = 983040 | Exact cap; no room for per-trial duplicate tables |
| Candidates 56*(2^49+2) | 31525197391593584 | Exact cap; existing generic theorem discharges it |
| Gate slots 4e15 | Conservative static screen ≤2701310063872 | Large margin; compiler slot theorem remains required |

The slot screen uses componentwise all-enabled primitive gate vectors (with 256-bit word payloads),
14 unary-query decoder overheads, 16 literal swaps (13326 slots each), and at most 514 optional
slots per endpoint word. It doubles the vector bound conservatively for record polarities, then
uses `56*(29*windowSlots+54634)`. Measurements are not gate slots. This is an analytical screening
bound, **not a kernel proof of `hg`**. Disabled `.whenBit` and `.recordGate` slots count too.

### Cheapest audited repair and alternatives

1. **Fuse the adjacent negations.** The last signed coordinate lookup ends in `windowYNegate`;
   the next segment starts with the same operation. `negativeModularNegateState_involution` plus
   coherent validity/frame facts permits deleting both: save **42868 T and 2044 M per odd window**.
   This requires cutting the final signed segment open, not deleting arbitrary source list elements.
2. **Use coherent uncompute in all 14 batch queries.** `BatchExecution.batchUnitary` and its
   coherent/model/frame theorems already give a mathematical spine. Compile its leaves with protected
   constant-bit gates and use a second CCX instead of each measured AND erasure. Add
   **7*458738 = 3211166 T/window**, remove 458738 records/window; width is unchanged.
3. **Prune the 3077 extra endpoint/comparator resets**, after proving these wires are clean after
   the full corrected window. `batchUnitary_fullFrame` / `placedBatchState_frame` are the existing
   evidence; full-window composition is still needed. Keep the old 854 reset labels and prove 837
   clean separately. This removes 3077 records/trial.

The repaired odd body is **517199074 T, 30272702 M**. With 854 resets, 56 trials hit the official
measurement cap exactly. Analytical full target: **3932 Q, T≤810996871160, Q×T≤3188839697401120**
(about 23,008× below the accepted baseline, conditional on a completed certificate).

A simpler repair preserving the current reset list replaces **460892 measured AND erasures per
odd window** by coherent cleanup: all 458738 batch erasures plus 2154 ordinary coordinate-QROM
erasures. It yields T≤811087730488, M=47471340336 (168 headroom), Q×T≤3189196956278816.
This is minimal for a uniform conversion count at 7 T/record with unchanged bodies/resets apart
from that conversion. It is more expensive than the fusion + pruning repair above.

An optional further reduction resets only the 513 accumulator wires between rounds and omits the
last reset. It frees 19609 records relative to 56×854; retaining that many measured query erasures
would save 137263 T, giving T≤810996733897. It adds compiler/position complexity for a tiny gain.
No global circuit-optimality claim is made: cheaper table layouts, control specialization or a new
correction algorithm could improve all of these. The recommended repair is the cheapest complete
low-width recipe priced here, using existing semantic interfaces.

## 3. Ordered milestones

| Milestone | Size | Checkable deliverable | Main risk |
|---|---|---|---|
| **M1: local T bridge and numeric audit** | **M, one session** | New `Entrant/Streaming/Costs.lean`; actual batch compiler/source T equality, placed correction numeric T, full core T bridge; coordinate/sign source counts; compile + allowed axioms + boundary | Transparent producer expansion during elaboration; keep lower compiler terms abstract |
| M2: repaired query compiler + local counts | M/L | `Streaming/CoherentBatch.lean`: protected constant-field query, coherent uncompute and source-model refinement, fixed M=0/T=6995548 for correction; append/shift/reindex WF/support/count/slot lemmas | Do not materialize Q-dependent literals; cost theorem must concern submitted syntax |
| M3: physical window and fusion | L | `Streaming/Window.lean`: fuse adjacent negations, actual window T=517199074/M=30272702, all optional gates WF, support≤3932; first lookup bounds | Sign order, valid canonical coordinates including infinity, zero flag 837 |
| M4: total coherent group-add and clean frame | L | Full corrected window equals signed `pointWrite` on encoded points; derive batch readiness/endpoint zeros and clean auxiliary frame; first lookup initialization | Finite/infinity split, route-label identification, branchwise phase cancellation |
| M5: heterogeneous outer budgets and reset | M/L | Compiling concrete entry/layout (parallel export only), exact finalCursor=47471340504, table/candidate limits, resource bounds; reset-to-zero with 854 resets | Uniform `OuterBudget` loses the tight M bound; pruning requires a real clean-subspace theorem |
| M6: Fourier law and decoder correspondence | XL | Actual entry's protected decoder event mass ≥99/100, from two-axis sampling, total probability and 56 reset trials | Generic record membership does not identify distribution; legacy raw approximation vs corrected total oracle |
| M7: assemble / replay / optionally switch Main | M | Instantiate `StreamingAssembly`; `Certificate officialLimits`; build, axioms, boundary, official scoring/replay and snapshot | Replay/proof-term scale; only report a score after checker success |

M2's correction T is `2*3211166+573216=6995548`. M3's body combines the fused coordinate
(`510203526 T`, its removed negation balanced by the retained final conjugation) and that correction.
These milestones can expose further arithmetic/sampling mismatches; do not schedule M6 as a trivial
`simpa` from the legacy theorem. Do not overwrite the working Main export until a second certificate
has built; no submission is authorized by this brief.

## 4. Verification and handoff

`workspace/StreamingAudit.lean`, checked by `formal-tools/check.sh`, confirms the key theorem names
and prints their transitive axioms. The audited assembly/resource, actual window execution,
coordinate/InPlace/Gidney/register correction, placed batch correctness/cost/frame, outer readout,
negation involution, table length, and legacy tight certificate use only `propext`,
`Classical.choice`, `Quot.sound` (some use a subset). No imported semantic theorem audited here
introduced an extra assumption disguised as a new axiom.

The legacy `StreamTightSupport` import needed building despite the fully built baseline: its
protected dependency build completed in 376s, including `RawNormalization` (123s) and
`StreamAssignedKernel` (77s). Only `.lake` build artifacts were produced outside Entrant.
Detailed command outputs are under `logs/streaming-*` (gitignored); the workspace checks and source
files are retained so their results can be regenerated. See HANDOFF for the final M1 build,
snapshot, and next action. No new SCOREBOARD row is appropriate for these unscored proof modules.
