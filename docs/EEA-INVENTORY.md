# Exact inventory of the measured EEA wrappers

Brief 12 inventory, 2026-10-29. Reproduce every number below with:

```sh
python3 workspace/eea_inventory.py
```

The calculator is an independent integer transcription of the protected source formulas at
bench commit `93051d2` (the protected tree is byte-identical to `origin/master`). It does not
count an expanded circuit. The main proof anchors are:

- `EEA/Windows.lean`: `certifiedActiveWindows`;
- `EEA/IntervalPrimitiveCounts.lean`: `intervalPrimitiveFormula9` and
  `intervalTraversalPrimitiveFormula`;
- `EEA/{BlockA,BlockB,BlockD,BlockE,BlockH}PrimitiveCounts.lean`;
- `EEA/IndexedStepPrimitiveCounts.lean`: `indexedStepPrimitiveFormula256` and the literal
  A--H split;
- `EEA/SchedulePrimitiveCounts.lean`: `secp256k1StepPrimitiveShape` and
  `secp256k1EEAForwardPrimitive_sum`;
- `EEA/Measured{And,BlockH,EndIteration,Schedule,ScheduleCounts}.lean`;
- `EEA/MeasuredPrimitiveCounts.lean` and `EEA/MeasuredWrapperCounts.lean`;
- `EEA/WrapperPrimitiveCounts.lean` and `EEA/PreprocessResources.lean` for the wrapper boundary.

## Exact reconciliation

One wrapper contains the fixed 1,620-index schedule. The already-adaptive A--H schedule has
17,454,225 CCX before the measured Block-H substitution. Block H replaces 1,681,736 coherent
cleanup CCX with the same number of X-basis measurement/reset erasures, leaving 15,772,489 CCX.
The wrapper boundary adds 137,526 CCX:

| Boundary component | CCX |
|---|---:|
| length initialize or uninitialize | 131,068 |
| centering comparator | 767 |
| two centering controlled-constant adders | 1,528 |
| parity controlled-constant adders | 1,528 |
| canonical work rotation | 2,620 |
| terminal epoch compression | 15 |
| **boundary total** | **137,526** |

Thus one measured wrapper is exactly **15,910,015 CCX = 111,370,105 T**. Each addition window
contains four such wrappers, hence

**4 × 15,910,015 × 7 = 445,480,420 T/window.**

This agrees with `MeasuredPrimitiveCounts.secp256k1MeasuredEEA{Forward,Reverse}Wrapper_primitive_exact`
and `InPlaceResources`. Across 28 windows it is 12,473,451,760 T/round.

## Cell and erasure census

The following are actual schedule occurrences in one wrapper:

| Item | Occurrences |
|---|---:|
| microsteps | 1,620 |
| every-fourth-step Block-H refreshes | 405 |
| Block-B interval calls | 3,240 |
| Block-B main-tree leaf visits | 977,908 |
| Block-B main-tree internal-node visits | 971,428 |
| Block-E coefficient-prefix calls | 3,240 |
| Block-E leaf visits | 572,070 |
| Block-E internal-node visits | 568,830 |
| Block-H upper/lower zero-map lanes | 53,316 / 52,400 |

The wrapper has exactly **6,961,844 measurement erasures**. This is not a proposal: these are
already in the frontier circuit.

| Existing measured-erasure class | Erasures/wrapper |
|---|---:|
| Block-B interval leaf/decoder | 2,925,752 |
| Block-E coefficient leaf/decoder | 2,281,800 |
| Block-H upper zero map | 848,196 |
| Block-H lower zero map | 833,540 |
| Block-G phase-update v-chains | 71,280 |
| centering comparator/adders | 766 |
| parity adders | 510 |
| **total** | **6,961,844** |

`MeasuredAnd.measuredAndErase_coherent_uncompute` is the branchwise theorem behind the local
zero-T cleanup. `CoefficientPrefixAdaptive_measurementCount` states two leaf-local and two decoder
erasures per leaf/internal-node pair. `MeasuredZeroMapCounts` and
`MeasuredEndIteration_savings` give the exact Block-H counts. Consequently, a rewrite which merely
re-applies measured AND erasure to these cells saves **zero**.

## Top ten nonlinear cells

Totals below include all four wrappers in one addition window.

| Rank | Cell class | CCX/window | T/window |
|---:|---|---:|---:|
| 1 | B measured interval ripple/decoder cells | 17,551,880 | 122,863,160 |
| 2 | E measured coefficient-prefix cells | 15,992,040 | 111,944,280 |
| 3 | A terminal tests, padding and preshift | 5,870,880 | 41,096,160 |
| 4 | H measured upper zero-map cells | 5,092,416 | 35,646,912 |
| 5 | H measured lower zero-map cells | 5,004,480 | 35,031,360 |
| 6 | F postshift | 3,667,680 | 25,673,760 |
| 7 | D quotient length/sign control | 3,604,728 | 25,233,096 |
| 8 | B interval endpoint prepare/restore | 2,695,680 | 18,869,760 |
| 9 | B surrounding controls | 1,283,040 | 8,981,280 |
| 10 | E boundary plus coherent controls | 1,036,800 | 7,257,600 |

These ten sum to 432,597,368 T/window. The remaining 12,883,052 T/window is the smaller A--H and
wrapper-boundary material printed by the calculator.

## Exact rewrite candidates

Only the first two rows currently have a complete source-level price. “Zero established” means no
eligible exact replacement theorem has yet been connected to that source cell; it is not a claim
that the algorithmic idea can never save T.

| Rewrite | Exact saving/window | Saving/round (28 windows) | Six-round saving | Proof effort |
|---|---:|---:|---:|---|
| Block-E middle: recreate the 2-bit temporary, MBU-erase `control`, then MBU-erase the temporary | **90,720 T** | **2,540,160 T** | **15,240,960 T** | M/L: local branchwise proof, then new step/schedule/compiler/count chain |
| Block-E held product: keep the temporary across the first coefficient scan, then MBU-erase both values | **181,440 T** | **5,080,320 T** | **30,481,920 T** | L: strengthen coefficient scratch cleanliness; current contract requires all `blockScratch` clean |
| One CCX removed in every microstep (conversion unit) | 45,360 T | 1,270,080 T | 7,620,480 T | depends on cell |
| Re-measure already measured B/E/G/H ANDs | **0 T** | **0 T** | **0 T** | none; already done |
| Phase-only comparison | **0 established** | **0 established** | **0 established** | L: all inspected wrapper compares produce a value consumed later; a phase-only interface must target a specific cleanup oracle |
| Shared identical products outside Block E | **0 established** | **0 established** | **0 established** | L: requires a clean donor and preservation proof; the source does not expose another priced repeated pair yet |
| Compile-time schedule specialization | **0 T** | **0 T** | **0 T** | done already: windows and `T % 4` Block-H presence are literal source functions |
| Replace full carry chains by Gold logical-AND ripple | **0 established** | **0 established** | **0 established** | L/XL: B/E/G already use measured ripple cells; wrapper constant adders need control/reduction and cannot be replaced by bare `chunk_add` |
| Horner multiply or square/subtract cell transplant | **0 established** | **0 established** | **0 established** | XL: separate semantic and resource chain; no source-compatible exact cell identified |

The conservative Block-E middle rewrite removes two cleanup CCX per microstep per wrapper:
`2 × 1,620 × 4 × 7 = 90,720 T/window`. At unchanged 855 Q and six rounds it projects
`T = 86,224,595,070`, score **73,722,028,784,850**, strictly below `ff1bf8d`. The held-product
variant removes four CCX/microstep and projects `T = 86,209,354,110`, score
**73,708,997,764,050**.

## Why the Block-E number is exact

`BlockEPrimitiveCounts.blockEAdaptive256_primitive` gives a fixed `160` CCX plus tree-dependent
work. Six CCX inside that fixed term are the two-bit control sequence:

1. prefix: compute temporary, compute subtraction control, coherently clear temporary;
2. middle: recompute temporary, coherently clear subtraction control, coherently clear temporary.

The conservative rewrite leaves the three prefix CCX intact. In the middle it pays one CCX to
recreate the temporary, then applies two zero-T measured erasures. Therefore the exact fixed term
falls from 160 to 158, independently of the coefficient window and measurement history. It adds
two records per microstep per wrapper: 3,240 records/wrapper, 12,960/window, 362,880/round and
2,177,280 over six rounds. This remains small relative to the frontier measurement budget, but
the certificate must still recompute all cursors and decoder positions rather than assuming that
margin.
