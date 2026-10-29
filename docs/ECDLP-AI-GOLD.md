# ecdlp.ai Gold → a challenge-certified circuit

Brief 07, source audit on 2026-10-29. **An exact Gold line exists: 2,841q → 2,820q, including sealed `gold-2820q-9619157c`. None of the inspected routes supplies an end-to-end Lean quantum-circuit theorem.** The smaller routes have substantial source representations, generated Rust and strong same-stream testing, but their missing channel, allocator and uniform-error theorems are explicitly recorded. A useful first deliverable is an exact carry/AND cell compiled from that source into the challenge's `Straight`, with a branchwise quantum proof and kernel-replayed resources. A full replacement is a research project measured in weeks to months, not a mechanical source export. [E/routes/gold-2820q-9619157c/{README.md,route.json}; E/routes/gold-1298q-e67e3563/contracts.json.]

## Evidence roots, scope and reproduction

| Prefix | Absolute path |
|---|---|
| E | `/mnt/c/code/ecc-formal-toolset` |
| R | `E/routes` |
| F | `E/formal/lean/EccFormal` |
| D | `/mnt/c/code/ecdlp-point-add` |
| G | `/mnt/c/code/secp256k1-point-add-spooky/.workspace/routes/ecdlp-gold-leapfrog-v1` |
| H | `/home/gitzard/shorecdlp` |
| B | `H/ShorECDLP/Submission/2607_13816` |
| L | `/mnt/c/code/shor-ecdlp-contest` |

Read-only checkout HEADs: E `da20c74c24a2bae2183c16b226a0a024666baa80`; D `b436000fe15aff093a9e1c653cc40a5cc1f0346a`; spooky `406a99051ed9345ae2861cc5740072fd23daacdc`; H `535a493f520dd7efe8c1cfc0b8b5a2741d5b35c1`. Individual route source hashes are stronger pins for untracked/frozen artifacts and are in the generated index. [Read-only `git rev-parse HEAD` at these roots; L/workspace/gold_artifacts.json.]

Every abbreviated path below expands using this table. Route IDs are literal directory names; `R/<id>/...` cites that particular epoch, not another route with the same width. Braces list separate paths. Local archived acceptance is reported as archived evidence, not a fresh server query. All donor repositories and the bench were read-only; **no Lean, Lake, Rust builder, evaluator, solver or route verifier was run**. Only lab Python calculators/indexers ran. This avoids both bench writes and accidentally running donor scripts that materialize large build trees. [User Brief 07; E/AGENTS.md; L/AGENTS.md.]

Read: lab HANDOFF/LOG/SCOREBOARD, PRIOR-WORKS, RELATED-WORK §4 and brief 06; E's AGENTS/README/routes inventory/descent playbook; route manifests, primary formal sources, archived axiom logs, selected generators and receipts. The indexer records **26 route directories, 213 formal files and 71 archived axiom logs**. It includes primary `formal/` trees, shared libraries and the formal-source sections of the 1337/1367 ZIPs; it excludes arbitrary scratch/build trees and does not audit all ~14,800 Lean files. `gold_artifacts.json` records theorem signatures **including premises**, paths, source hashes, native shortcuts and per-theorem archived axioms. A file's existence or a header is not a verified theorem. Source scope is explained below; absent receipt information is marked unknown. [L/workspace/{gold_route_inventory.py,gold_artifacts.json}.]

Reproduce the read-only indexing and arithmetic from the lab:

```sh
python3 workspace/gold_route_inventory.py --output workspace/gold_artifacts.json
python3 workspace/gold_costs.py
```

`docs/ECDSAFAIL-TRICKS.md` completed during this audit and was cross-checked before handoff, together with `workspace/ecdsafail_tricks_costs.py`. This report uses the same **464 binary additions, 513-bit point encoding, 7,182-T dummy-control wrapper and 573,216-T singleton correction** conventions, and gives the overlap/disjoint-workspace assumptions explicitly. Brief 06's reusable-bank 4,106-Q design assumes arithmetic/correction workspace overlap; the conservative disjoint Gold1240 example here instead uses 4,834 Q. It does not inherit hypothetical exact-core costs as proofs. [L/workspace/ecdsafail_tricks_costs.py; B/Challenge/{BatchCost,BatchPlacement,OuterResources}.lean.]

## 1. Route inventory

`S` below means **emitted/static CCX+CCZ**, an all-enabled upper bound on executed nonlinear gates in the native stream, not necessarily an attainable branch maximum. The challenge requires a natural-number **worst-case T bound after lowering**. CCZ lowers to H–CCX–H, CZ to H–CX–H, Z to H–X–H; hence `7S` is a native-stream proxy before additional guard logic, classical arithmetic, control and hardening. Mean Toffoli never supplies S. Unknown S remains unknown; `S ≤ emitted operations` is a valid but very loose native count bound. Q below is the donor's measured peak, not yet the challenge's proved union of wire labels. [H/ShorECDLP/Framework/{CostModel,Quantum/Adaptive,Quantum/MeasurementUncompute}.lean; R/gold-1298q-e67e3563/generation/runtime.rs.in.]

`A` = approximate; `E*` = classified exact/no named bad events, **without a whole-circuit Lean theorem**. `L1024k` is a local 1,024,000-shot clean cohort; `S102k` is archived server 102,400-shot acceptance; these are separate cohorts and are not added together to imply independent statistical certainty. Means from different cohorts differ legitimately. Formal-family codes refer to the file-level inventory below. Each row's default source is its own `route.json` and `validation/expected.json` when present; explicit exceptions follow the table.

| Route under R/ | Q | S emitted CCX+CCZ | Mean executed Toffoli (cohort specified where needed) | Clean shots / status | Kind | Formal family |
|---|---:|---:|---:|---|---|---|
| `gold-1198q-dd745c8c` | 1,198 | 2,152,612 | 2,012,476.486887 deep | L1024k; no server claim | A | W + inherited H |
| `gold-1227q-803657d6` | 1,227 | 2,056,154 | 1,912,138.687 local | local102k passed; **server failed**, one mismatch at shot 67,677 | A, invalidated | J |
| `gold-1239q-1e5b9d86` | 1,239 | 2,114,978 | 1,974,844.391131 deep | L1024k; no server claim | A | T + inherited H |
| `gold-1240q-fef245d4` | 1,240 | 2,114,708 | 1,974,707.404 stock; **1,974,705.988 deep** | L1024k + S102k | A | H |
| `gold-1283q-b9ab2819` | 1,283 | unknown; ≤12,377,821 ops | 2,502,170.191 stock; 2,502,173.425 deep | L1024k + S102k | A | Q |
| `gold-1286q-fb501d96` | 1,286 | unknown; ≤22,882,730 ops | 1,056,742.677494 deep | ten fresh stock cohorts totaling L1024k; no server claim | A | N + X |
| `gold-1298q-e67e3563` | 1,298 | unknown; ≤21,064,276 ops | 1,031,994 rounded local; **1,031,988 rounded trusted** | L1024k + S102k | A | N |
| `gold-1299q-d912955f` | 1,299 | 1,171,372 | 1,074,110 rounded local; 1,074,109 trusted | L1024k + S102k | A | V |
| `gold-1299q-e6550537` | 1,299 | 1,119,996 | 1,039,062 rounded local; 1,039,061 trusted | L1024k + S102k | A | V + delivery |
| `gold-1337q-877af1c6` | 1,337 | unknown in inspected summary receipts | 1,068,707.472 stock | L1024k + S102k overlay | A | U + inherited P |
| `gold-1367q-762f4fcc` | 1,367 | 1,303,454 | 1,169,470.589395 stock | L1024k + S102k overlay | A | P |
| `gold-1401q-b1c6dbc8` | 1,401 | unknown; ≤57,066,322 ops | 7,304,922 | local102k | A | C17, **native axioms** |
| `gold-1402q-50ab5c0a` | 1,402 | unknown; ≤63,897,722 ops | 8,847,079 | local102k | A | C5, **native axioms** |
| `gold-1435q-1eb91f0a` | 1,435 | unknown; ≤63,235,676 ops | 8,783,503 | local102k | A | PP + Leader52 |
| `gold-1435q-80575711` | 1,435 | unknown; ≤63,235,580 ops | 8,783,503 | local102k | A | PP |
| `gold-1466q-23608d60` | 1,466 | unknown; ≤60,226,490 ops | 8,495,507 | local102k | A | C5 base |
| `gold-1499q-c0ec991a` | 1,499 | unknown; ≤59,626,388 ops | 8,410,915 | local102k | A | K |
| `gold-1627q-609867b4` | 1,627 | unknown; ≤53,650,878 ops | 7,842,114 | local102k | A | B9 + CrossProductSquare |
| `gold-1669q` | 1,669 | unknown; ≤53,657,413 ops | 7,856,446 | local102k + S102k | A | B9 |
| `gold-2820q` | 2,820 | unknown; ≤41,431,550 ops | 5,211,740 | local102k + S102k | E*, historical unsealed | E3 |
| `gold-2820q-9619157c` | 2,820 | same unknown S as previous row | 5,211,740 | local102k reverified + same S102k | E*, **same epoch**, sealed | E3 + seal |
| `gold-2841q` | 2,841 | unknown; ≤40,922,095 ops | 5,180,781 | local102k + S102k | E*, unsealed | ExactTargetFanout |
| `ecdlp-1626q-vented` | 1,626 | unknown; ≤25,427,696 ops | 4,599,075 | local102k | A, Bronze+ | VentedReplayCleanup |
| `ecdlp-1626q-f4` | 1,626 | unknown; ≤24,132,822 ops | 4,466,726 | local102k | A, Bronze+ | F4FusedAdd |
| `ecdlp-1626q-f6` | 1,626 | unknown; ≤23,751,616 ops | 4,335,399 | local102k | A, Bronze+ | F6SplitWitness |
| `ecdlp-1669q-f8` | 1,669 | unknown; ≤50,517,829 ops | 7,594,814 | local102k | A, retired as descent | ComparatorFusion |
| G, Gold Leapfrog **epoch 11** | 1,286 | unknown; ≤17,572,178 records | 960,091.439 stock; **960,096.46 deep**; model 960,096.5 | local102k + L1024k; S2 source/native admission | A | LF source; no full Lean theorem located |

Additional row sources: R/{gold-1298q-e67e3563,gold-1286q-fb501d96}/README.md and `evidence/{seal.json,origin/epoch.json,origin/summary.json}` as applicable; R/gold-1299q-{d912955f,e6550537}/`evidence/canonical-native-records.json`; E/README.md for early accepted metrics; R/gold-1337q-877af1c6.{promotion,server-acceptance}.json and R/gold-1367q-762f4fcc.{ecdlp-submission,server-acceptance}.json overlays; G/notes/epoch11-result.json. The 1337 table mean is archived stock, not trusted score divided by Q. Static counts are not inferred from those means. The two 1435 rows' operation count is taken from their manifests. [Those paths; machine records in L/workspace/gold_artifacts.json.]

`D/dist/submission-note.md` and `submission-metadata.json` bind the **1240q fef245d4** stream: S=2,114,708, 11,541,887 emitted operations, 569,051 classical bits. Rounded metadata mean 1,974,707 is the 102,400 cohort; the note's 1,974,705.988 is the million-shot audit, explaining the apparent discrepancy in the brief. `D/results.tsv` is historical run evidence, not a current resource theorem. The 1286q epoch-11 route G is distinct from E's later 1286q fb501d96 route and has different source, cost and stream. [D/dist/{submission-note.md,submission-metadata.json}; G/notes/epoch11-result.json; R/gold-1286q-fb501d96/evidence/origin/epoch.json.]

The 1626 rungs are useful donors but recorded as back-derived, patched generated Rust; F8 is genuinely emitter-derived yet ineligible under that lab's qubit-descent naming rule and still has open physical-disjointness/hash-binding obligations. Those provenance labels do **not** determine mathematical eligibility here: a new challenge proof could certify any sound reconstruction. They do prevent inheriting the old label or treating a reproducibility receipt as a semantic proof. [R/ecdlp-1626q-{vented,f4,f6}/route.json; R/ecdlp-1669q-f8/route.json; E/docs/gold-descending/lineage-provenance-audit.md.]

### What “exact” answers, and what remains open

There **is** a no-bounded-bad-event route, so the answer is not “all Gold is approximate.” Sealed 2820 explicitly has `classification: exact`, `named_bad_events: []`, the same stream as historical 2820, and `whole_circuit_correctness_from_local_proofs: false`. Its arithmetic authority is local square algebra, a double/halve identity and local fanout rewrites; five payload files include a separately frozen integration `mod.rs`. **No inspected theorem proves that complete emitted point-add channel equals total secp256k1 translation on the challenge encoding.** Exactness is the route's declared algorithmic assurance, not a complete kernel certificate. Identity, doubling, inverse pairs, infinity, zero denominators and arbitrary phase-clean ancillas still need an actual interface theorem before Shor use. [R/gold-2820q-9619157c/{README.md,route.json,generated/MANIFEST.json,evidence/receipt.json}; F/PointAddAlgorithm.lean.]

## 2. What the formal files establish

These are **scoped results**, with archived kernel claims where supplied, not new replays. The detailed index has every indexed theorem signature and its explicit premises. `authority_boundary` theorems frequently prove that a Boolean flag saying “whole circuit proved” is false: they correctly limit scope but are not channel proofs. Hash literals and recorded shot-count equations similarly prove arithmetic about literals, not that the evaluator produced them. [L/workspace/gold_artifacts.json; e.g. R/gold-1240q-fef245d4/formal/lean/Gold1283FrontierNative270GoldAdmissionV466.lean.]

Axiom notation below: `0`=none, `P`=`propext`, `Q`=`Quot.sound`, `C`=`Classical.choice`; `≤PQC` means each printed theorem uses a subset of that set. It is **not** a claim about every unprinted declaration or its imports. `?` means no per-theorem axiom transcript established in this inspection. Per-theorem entries, rather than the module-wide union, are in the JSON. Historical 4.15 evidence cannot be imported into bench **4.28.0** as binary objects; newer 4.29.1 files also need a source port. [H/lean-toolchain; E/formal/lean/lean-toolchain; archived paths below.]

### Shared binary-GCD and exact families

| Family / files | Actual theorem scope | Version / archived axioms |
|---|---|---|
| B9: F/`PointAddAlgorithm.lean` | Affine register formulas and slope cleanup, **given** nonzero denominators and correct division/multiplication relations | shared package currently 4.29.1; route historical version not independently recovered; B9 README reports ≤PQC |
| F/`BinaryGcdConvergence.lean` | Exact selected Algorithm-2 steps decrease bitlength potential; **511** selected/padded rounds reach `(1,0)` under canonical nonzero/coprime input premises | same; does not certify the other families' 270/741/750-round schedules |
| F/`BinaryGcdGarbageReplay.lean` | Trace reversal and coefficient replay orientations; value-state relations | same, reported ≤PQC |
| F/`BinaryGcdInPlaceMultiplication.lean` | In-place multiplication relation from those value/replay contracts | same |
| F/`BinaryGcdPhysicalRelease.lean` | Value-level high-wire zero/release premises, seven-scratch capacity arithmetic | same; not emitted allocator/channel refinement |
| F/`BinaryGcdUniformLedger.lean` | Public component widths and persistent capacity ledger | same |
| F/`ApproxReplayBadEvents.lean` | Local exactness off a bad predicate composes **along actual approximate visited states**; final mismatch implies some premise failed | pure logical induction; no probability measure or numerical bound; archived axiom detail ? |
| F/`LoanAwareHybridAdder.lean` | Masked/controlled addition values and loan cleanup | value/Boolean scope; target Gidney/HMR gate proof explicitly pending |
| F/`PrefixComparator.lean` | Prefix order agrees with full order off equal-prefix/low-suffix bad event | no probability or physical comparator proof |
| F/`CrossProductSquare.lean` (P1/1627 extra) | Ring square/cross-product algebra and source-schedule agreement | kernel claim in R/gold-1627q-609867b4/formal/README.md; exact axiom transcript ? |
| E3: F/`ExactProductSquare.lean` | Karatsuba/five-term square identity, with `B²=F` fold premise | PQ for the two ring identities |
| F/`ExactSolinasWalk.lean` | n doublings then n multiplicative halvings restore input, **assuming** `2*half=1`; numerical signed NAF coefficient identity | P |
| F/`ExactTargetFanout.lean` | Boolean basis action of `CCX;CX;CCX → CX;CCX`, enabled/disabled; commuting contexts require explicit commutation premises; adjacent X cancellation | 0 for printed rewrites, including context theorem |
| R/gold-2820q-9619157c/formal/lean/`SealArithmetic.lean`, `PantographSeal.lean` | Literal qubit/score arithmetic and peak descent | seal receipt **4.15.0**; exact E3 logs in `evidence/lean-kernel.log`; not an ECC refinement |

Sources for B9 mapping: R/gold-1669q/formal/README.md and INPUTS.json; P1 mapping: R/gold-1627q-609867b4/formal/README.md. Exact logs: R/gold-2820q-9619157c/evidence/{lean-kernel.log,formal-toolset.receipt.json}. Auxiliary F/`PseudoMersenne{TruncatedCorrection,ApproxDouble,ApproxControlledAdd}.lean` isolate carry-window, missed-reduction and prefix-cleanup predicates; their theorems are **conditional equality off bad events**, not density estimates. The `formal/lean429/BinaryGcdGarbageReplay.lean` edition is another version-specific artifact, not a proof that the bench can import it unchanged. [Those files; L/workspace/gold_artifacts.json.]

### Small-width hybrid routes: W, T, H, Q

All named files here are under the route's `formal/lean/` unless otherwise stated. The 1198 receipt reports **Lean 4.29.1**, seven local contracts, not a full circuit theorem. The 1240/1283 receipts and E's current policy use 4.29.1; verify the frozen epoch/toolchain again on a future port. [R/gold-1198q-dd745c8c/evidence/kernel.receipt.json; E/README.md.]

| Route/family and file | What it proves | Axiom evidence |
|---|---|---|
| W/1198 `FullSubtract.lean` | Full-width modular borrow correction; preserving a parent's good domain | PQ |
| W `WindowRefinement.lean` | Windowed add/sub agrees when correction fits the selected window | PQ |
| W `WindowMonotonic.lean` | 60/62/63-bit supported corrections remain supported in widened window | PQ |
| W `WindowWitnesses.lean` | Three concrete old-window failures/new-window successes | 0 |
| W `PrefixRefinement.lean` | Strict high-prefix comparison implication; concrete old/repaired witness | ≤PQ |
| W `ControlledRegisterProvider.lean` | Full-adder cell forward/reverse and arbitrary-width word-value induction; controlled output-carry roundtrip and source restoration | ≤PQ |
| W `MeasuredComparator.lean` | Complement/ripple carry computes `<`; defining product and all-outcome **Boolean phase bookkeeping** repair; input restoration | ≤PQ, still needs bridge to bench Kraus semantics |
| T/1239 `FusedTwoBitTail.lean` | Two-bit tail forward/inverse, retained carry and all-outcome phase identities; selected production-tail condition | ≤PQ |
| T `CleanupCarryPartition.lean` | Carry/borrow duality, high/low partition transplantation, ripple boundary/equality predicate | ≤PQC |
| T `Gold1240FrontierTagged1239ComparatorGateRefinement.lean` | Boolean gate-borrow equals arithmetic borrow; ripple induction, equality is not less, conditional physical acquire bound | file/signatures indexed; independent axiom transcript ? |
| H/1240 `Gold1283FrontierNative270ThirdResidualRepairV453.lean` | Strict high-prefix ordering implies full ordering; **four concrete K2 minima** and one concrete cleanup minimum | ≤PQC; universal compare/cleanup-support flags are false |
| H `Gold1283FrontierNative270GoldAdmissionV466.lean` | 1283→1240 literal descent; 14,708 emitted-gate band excess; false sampling/universal authority flags | theorem is admission arithmetic; separate axiom transcript ? |
| Q/1283 `Gold1401QartonSemanticBridge.lean` | Qarton/parent affine values agree given nonzero dx and correct quotient/product; no finite-width/cleanup theorem | ≤PQC |
| Q `Gold1401ClassicalCoordinateAdapter.lean` | Copy/unload classical bits into clean word and restore them; arbitrary-width value/cleanup | Q on printed adapter identities; no intervening arithmetic/whole allocator proof |
| Q `Gold1401HybridEpoch.lean` | Frozen resource/owner numbers, operation-expansion arithmetic, conditional value composition, literal hashes | 0 on printed arithmetic; literals do not attest an external run |

Axiom sources: W `evidence/lean/<module>.log`; T `evidence/origin/{fused-two-bit-tail-v1,cleanup-carry-partition-v1}/kernel.log`; H `evidence/logs/frontier-native270-third-residual-repair-v455.lean.log`; Q `evidence/{gold-1401-qarton-semantic-bridge.lean.log,gold1401hybrid/{classical-adapter,hybrid-epoch}.lean.log}`. T/H reuse earlier contracts through source manifests; a route-local file count is not the complete dependency closure. [Those paths; respective INPUTS.json.]

### Signed ping-pong routes: P, U, V, N, X

P/1367 formal files are inside `R/gold-1367q-762f4fcc/provenance/frozen-inputs.zip!route/formal/`; the **21 checked modules** are named in `evidence/package-kernel-v2.json`, toolchain **4.29.1**, with theorem axiom output in `evidence/kernel/<module>.log`. Older V1/V2 drafts also remain in the archive: existence does not upgrade them to the final checked version. The index preserves their signatures separately. [Those paths.]

| P checked file(s) | Scope | Axiom union of printed declarations |
|---|---|---|
| `CarryPhysicalCellV1.lean` | Local Boolean gate interpreter, forward carry and measured sum/compare unwind, arbitrary outcome and incoming phase; guarded variant | 0 |
| `LinearMaskPhysicalCellV2.lean` | Implicit linear-source carry, all-outcome unwind and doubled-flag cleanup | 0 |
| `FusedConstantCellV1.lean` | Constant first-borrow/low-sum cell | 0 |
| `TerminalPhaseV1.lean` | Majority-phase identity, guarded/no-incoming terminal repair | 0 |
| `CarryRepairV2.lean` | Local vs full-prefix carry predicate, equality witness, correct vs wrong predicate phase | ≤PQC |
| `SignedWalkV3.lean` | Odd numerator/quotient, inverse identity, carry/history/top-bit/loan relations and bounded signed decoding | ≤PQ; not universal termination |
| `HistoryRecoveryV3.lean` | XOR/parity history recurrence and missing-bit recovery, deferred phase | ≤P |
| `FusedInitialV1.lean` | Sparse initial forward/reverse masks, exclusive arms, initial-source/constant and lift premises | ≤PQC |
| `CanonicalHalveRowV2.lean` | One-hot selector, borrowed carry, correction/evenness/high bit; row correctness **off slice bad event** | ≤PQ |
| `CanonicalMultiplyRowV1.lean` | One-hot selector/source fold, off-slice row equation and post-fold mismatch predicate | ≤PQ |
| `CanonicalEndpointsV2.lean` | Canonical add/halve/double corrections, seed and inverse pre-XOR/shift-flag cleanup | ≤PQ |
| `AffineCoordinateV2.lean` | Full-adder bit identity, bounded once/twice reduction, triple reduction, affine x/y algebra | ≤PQ |
| `SplitMaskV1.lean` | Source/target restoration, terminal majority, output sum, low boundary and controlled negation value | ≤PQ |
| `SquareTriangularV5.lean` | Triangular-step integer identity and framed-row inverse | PQ |
| `SquareWordBoundaryV1.lean` | Row deltas and no-wrap **under explicit range premises**, active radix and correction mod equation | ≤PQ |
| `SquareModularV2.lean` | Three-branch square decomposition, shift/rotation and NAF constants | ≤PQ |
| `RecursiveSquareDonorExact.lean` | Recursive square algebra/width shape, ordered child cleanup; counterexample to premature low mutation | ≤PQC |
| `lean/reuse-v1/ControlledRegisterProvider.lean` | As W provider above | ≤PQ |
| `lean/reuse-v1/MeasuredComparator.lean` | As W comparator above | ≤PQ |
| `lean/reuse-v1/ExactDonorChunk.lean` | Partition-independent addition, measured carry, overflow-from-sum, phase transport under context | ≤PQ |
| `lean/reuse-v1/PingPongSeedLift.lean` | Bit-one/odd/signed-range lift and reverse modular equation | ≤PQC |

U/1337 source is in `R/gold-1337q-877af1c6/provenance/source-inputs.zip!formal/`; twelve local files extend P. They use **4.29.1** according to E/AGENTS.md's route description and sealed admission; a fresh per-theorem axiom audit of the archive's U modules is still required (not inferred from P). [R/gold-1337q-877af1c6/{route.json,evidence/admission-audit.json}; E/AGENTS.md.]

| U file | Actual scope |
|---|---|
| `AsymmetricResidualReverseV1.lean` | Exact half/unhalf and inverse reconstruction, given evenness and capacity |
| `BoundedPrefixPhaseV1.lean` | Phase discrepancy equals explicit bad predicate; off-bad equality; **incoming-equality counterexample** |
| `CheckpointScheduleV1.lean` | Independent walk/replay commutation, list append and inverse composition |
| `Fold68RefinementV1.lean`, `Fold72RefinementV1.lean` | Smaller-window fold agrees with larger one **if no wrap**; divide/multiply equations under that premise |
| `PrefixComparatorWordV3.lean` | Decoded word/prefix comparison exact off explicit low-suffix bad event; carry predicate |
| `RawCapacityHalfV1.lean`, `WideHalfStepV3.lean` | Bounded signed half/restoration and doubled-word bound; concrete failing round 646 witness in the latter |
| `RawWorkingWidthV1.lean` | Chosen working width covers required operands/raw intermediate; extension omission iff range condition |
| `RetainedHighWordV1.lean` | Reframing preserves value; release requires sign extension; advance/undo keeps high information |
| `SplitWalkBudgetV2.lean` | Chosen checkpoint split fits and is minimal in its numerical model; cost/scratch equation |
| `TerminalCoefficientV4.lean` | Canonical divide/multiply endpoint equations and phase agreement conditional on predicates |

V files are directly under `R/gold-1299q-{d912955f,e6550537}/formal/`. Their canonical log directories `evidence/canonical/proofs/` report **only allowed axioms**, with **4.29.1** source replay stated in the route READMEs. The same file name in both epochs is not permission to reuse one epoch's resource/stream receipt for the other. [Those READMEs/logs.]

| V/N/X file | Actual scope | Printed axiom union |
|---|---|---|
| V `RawSignedFrameV2.lean` | Orientation/quotient/remainder and exact integer reverse step, determinant | PQC |
| V `RegrowingWidthV1.lean` | Signed encode/decode roundtrip **if value fits**; widening/regrowing and half support | PQC |
| V `TerminalBackwardEnvelopeV1.lean` | Bounds on predecessor **given endpoint and recurrence**, intersection with forward bound | PQC; not convergence |
| V `DeferredCarryRepairV1.lean` | Inverse carry decomposition and outcome-combination/cancellation with recomputed predicate | PQC |
| V `RollingCarryRecoveryV2.lean` | Current cumulative prefix recovers carry; stable low residue and phase if predicates equal; 36-bit witness | PQ |
| V `ParityWireLoanV1.lean` | Low-digit, first-carry phase and tail/low-zero restoration | PQ |
| V `GroupedReplayCommutationV1.lean` | Independent product-state raw/coefficient actions and batches commute with shared read-only controls | P |
| V `NativeHybridGuardV1.lean` | Duplicate/ distinct control identities and guarded phase | 0 |
| e655 `Sub1300DeliveryV1.lean` | Profile capacity **conditional** on requirement bound; strict-prefix33 ordering; literal delivery arithmetic | PQC |
| N/1298 `WitnessEnvelopeV10.lean` | **`terminalRound ≤ 741 → terminalRound ≤ 750`**, width-widening implication, unequal high-prefix34 order, zero add, resource arithmetic | ≤PQC on same named module's 1286 admission logs; 1298 independent transcript ? |
| X/1286 `PrefixRepairV1.lean` | Carry equals wrapped-sum `<` predicate, higher writes preserve low prefix; includes **incoming carry equality**; phase cancellation if recovered=actual | ≤PQC |
| X `ExactSplitBudgetV1.lean` | 1286q score threshold; measured budget misses target; base16 carry-from-prefix identity | ≤PQC |

N's `terminal_refines_parent` is particularly easy to overread: it does **not** show any input terminates by 741. X adds generated small-operation all-input/outcome SMT queries and finite lifecycle evidence, without proving universal wide-word quantum refinement. [R/gold-1298q-e67e3563/formal/WitnessEnvelopeV10.lean; R/gold-1286q-fb501d96/{formal/PrefixRepairV1.lean,generation/prove.py,evidence/admission/formal/}.]

### Earlier compressed-tape descendants and non-Gold donors

| Family / file under its route's `formal/lean/` unless specified | Actual scope / missing bridge |
|---|---|
| K/1499 `P1BlockedReplay.lean` | Two-block integer reconstruction, boundary carry cleanup, declared 128-owner saving; forward/inverse replacement **premises**, no emitted channel theorem |
| K `P1BlockedComparatorV2.lean` | Lexicographic blocked `<`, sparse thresholds, literal score arithmetic |
| K `P1LowOwnerSquare.lean` | Primitive-selection value algebra and static owner counts; assumes primitive semantics |
| K `P1Jump2Retiming.lean` | Parent-trace retiming/inverse, selector soundness for selected branches; named missing-258-row-witness event, declared disjoint owner ranges, bounded signed word permutation; not whole-walk convergence/lowering |
| C5-base/1466 `Base3Tape.lean`, `Audit.lean` | Reachable three-symbol alphabet, 5-trit/8-bit encoding/decoding, 34-bit saving and literal ledger; Audit prints axioms |
| PP/each1435 `PingPongSignedOdd.lean` | Ideal signed odd-cell residue selection, quotient/inverse and coefficient roundtrip; not physical low-bit classification/termination |
| PP `PingPongGoldRefinement.lean` | Functional ping-pong and three-stage schedule factorization, append/roundtrip, known-one loan under semantic/independence premises |
| PP `PingPongFourBlockReplay.lean` | Four-block arithmetic/comparison; boundary carry includes incoming-equality arm; declared owner/score arithmetic |
| PP `PingPongHybrid{WalkComparator,ControlledAdder}.lean` | Boolean cell or split/recombine value identities and conditional hybrid owner/cost model; not universal HMR/allocator proof |
| PP `PingPongClassicalBitPool.lean` | Last-use overwrite/sequential reuse model; historical ID-cap arithmetic; not emitted liveness |
| 1435-1eb `Leader52Donation.lean` (namespace Leader52) | Stable schedule/approximation literals, X-pair nonce identity, default override and named bad-event enumeration |
| C5/1402 `InterleavedSlice.lean` | Independent updates commute, parent trit codec and inverse composition |
| C5 `PackedTapeResidency.lean` | Middle unpack/repack elimination under inverse premise; nominal score envelope |
| C5 `HmrPackerUncompute.lean` | Boolean measurement/CZ phase cancellation, cleanup-value equality and literal packer savings |
| C5 `SchedulePortBoundary.lean` | Branch-alphabet obstruction, 511-round partition arithmetic, list schedule composition |
| C5 `FourBlockBase3Composition.lean` | g5/bank64 conditional composition and literal resource/score arithmetic; **uses native_decide** |
| C5 `Pantograph{Slice,Composition}.lean` | Independent product updates and literal bank reuse peak, supporting goals only |
| C17/1401 `G17Low73Composition.lean` | g17 tape width/cap arithmetic and low73 doubling equality off named bad events; **uses native_decide** |
| C17 `MeasuredEpoch.lean` | Literal measured Q×mean score and descent arithmetic |
| 1626-vented `formal/VentedReplayCleanup.lean` | Canonical dance selector, parity/add/halve flag cleanup and packing bound (I1–I5), no physical/HMR theorem |
| 1626-f4 `formal/F4FusedAdd.lean` | Mutually exclusive modular-add correction witnesses, predicate, value and canonical range |
| 1626-f6 `formal/F6SplitWitness.lean` | Post-sweep value and disjoint split witnesses; explicit counterexample to using ov1 alone |
| 1669-f8 `formal/ComparatorFusion.lean` | Old two-comparator and fused one-comparator actions equal **given restored sweep + disjoint flag-consuming body**; two abstract consumer shapes instantiated; physical emitter alias proof still open |

Versions/axioms: C5/C17/1466 and both1435 receipts explicitly report **4.15.0**, with Pantograph **4.29.1** a separate supporting lifecycle tool. K/1499's historical checking claim exists but the precise original version/complete axiom list was not recovered here; current shared package pin alone does not settle it. C5/C17 logs exhibit **`Lean.ofReduceBool`**, forbidden by this challenge. Reprove their finite sums/bounds with kernel arithmetic/induction. B9/P1 and the 1626/F8 sources also require fresh version/axiom replay; vented log shows ≤PQC, F6 route explicitly reports PQ, and F8 report shows 0/P. F4 exact per-theorem axiom set remains ?. [R/gold-{1466q-23608d60,1402q-50ab5c0a,1401q-b1c6dbc8}/evidence/formal-toolset.receipt.json; R/gold-1435q-{1eb91f0a,80575711}/evidence/lean-kernel.receipt.json; R/gold-{1401q-b1c6dbc8,1402q-50ab5c0a}/evidence/{g17-lean.log,four-block-composition-lean.log} respectively; R/ecdlp-1626q-vented/formal/vented-cleanup.lean.log; R/ecdlp-1626q-f6/route.json; R/ecdlp-1669q-f8/evidence/F8-LEAN-REPORT.md.]

Invalidated J/1227's three `Gold1283FrontierNative265{DonorExactRewriteV316,K2Guard8V302,GoldAdmissionV324}.lean` files prove local Boolean rewrite identities, observed-deficit/guard monotonicity, price literals and zero **recorded local** failures. The server counterexample supersedes that local admission, without making the local identities false. [R/gold-1227q-803657d6/formal/lean/; R/gold-1227q-803657d6.server-invalidation.json.]

### Z3, TLA+ and Pantograph: exact scope of the auxiliary files

No Z3/TLC result is automatically a Lean proof or an allowed axiom. Source/backend agreement and tests are useful evidence; they must be translated into kernel lemmas or replayable certificates for the submitted theorem. Pantograph reuses checked Lean interfaces; a lifecycle seal adds no mathematical assumption discharge. [E/docs/gold-descending/{05-formal-toolset,14-formal-route-admission}.md; R/gold-1286q-fb501d96/generation/prove.py.]

| Files / family (relative to indicated `formal/`) | What the check establishes |
|---|---|
| E `z3/exact_{product_square,solinas_walk,target_fanout}.py` | Counterexample UNSAT queries for five-term square/fold, 22-double/halve restoration/NAF, Boolean fanout/X-pair identities; not whole Rust refinement |
| E `z3/point_add_algorithm.py`, `kaliski_space_envelope.py` | Field/register algebra model; finite **10-bit** legal-branch width potential and explicit witnesses, respectively |
| K `z3/p1_architecture_fit.py`; PP `z3/{leader_fit,pingpong_fit}.py` | Width-pinned 257/259-bit arithmetic/known-one/score fits and negative controls; no whole-run input support theorem |
| C5-base `z3/base3_threshold_recovery.py` | Fixed finite trit code's threshold recovery, not physical packed-tape phase |
| C5 `z3/{slice_fit,composite_budget,hmr_packer_budget,packed_residency_budget}.py` | Selected finite slice equivalence or integer budget envelopes/negative controls; not a physical owner ledger |
| C17 `z3/g17_fit.py`; Q `z3/gold_1401_hybrid_epoch.py`; E3-seal `z3/seal_fit.py` | Frozen owner/resource/score integer fits; not arithmetic channel proofs |
| J `z3/{check_native265_donor_rewrite_reserve_v53,native265_k2_guard8_v302_miter,native265_owner_stable_cleanup_v6_miter}.py` | Local Boolean rewrite/guarded miter, observed deficits and reserve arithmetic; no universal reachable support |
| H `generation/check_native270_third_residual_repair_v455.py` | Bounded strict-prefix implication and five concrete minima; no input-distribution theorem |
| X `generation/prove.py` + `evidence/component/programs.json`, `formal/exact_split_carry.smt2` | **14** generated small-operation all-input/all-outcome queries plus a carry query; does not lift those finite sizes to all 256-bit callers |
| U archive `scratch/prefix40-all-widths-v1/*.smt2`, related negative/fold queries | Width-specific word/prefix phase checks; scratch cases are not all-input probability bounds |
| P archive `route/build/square-core-z3-v*/...` | Selected row/triangle/recursive-copy sizes and negative examples; historical build queries, outside the primary 213-file index |

TLA+ files and their modeled responsibilities are: E/formal/tla/`{CleanPointAddWorkflow,SplitKaliskiSpace}.tla` (workflow/space lifecycle); K `P1OwnerLifecycle.tla`; PP `LeaderLoanLifecycle.tla` / `PingPongLoanLifecycle.tla`; C5-base `BranchTapeGroup.tla`; C5 `{CompositeBankLifecycle,PingPongSliceLifecycle}.tla`; C17 `G17OwnerLifecycle.tla`; Q `Gold1401HybridOwnerLifecycle.tla`; H `FrontierNative270ThirdResidualRepairV453.tla`; T `FusedTwoBitTail.tla`; E3-seal `SealLifecycle.tla`; J `FrontierNative265{DonorRewritePassV53,K2Guard8V302,OwnerStableCleanupV6}.tla`. They explore finite abstract acquire/use/release or admission sequences with configured invariants, sometimes a rejecting mutant. They do not evaluate secp256k1 coordinates or all physical wire aliases. [Those files under each route's `formal/tla/`; accompanying `.cfg`/formal-toolset receipts.]

P's ZIP additionally contains `AffineOwnershipV1`, `CanonicalHalveOwnerV1`, `CanonicalRowOwnerV1`, `CarryRepairOwnerV{1,2}`, `CheckpointLoanV1`, `FusedInitialOwnersV1`, `HistoryOwnersV1`, `SignedWalkOwnersV1`, `SquareRetainedV1` TLA files: abstract phase ownership, no wide quantum refinement. X's `{PrefixOwnerV1,RetainedOwnerV1,ExactSplitOwnerV1}.tla` explore **5, 9, 6 states** respectively; this is precise small-model evidence, not an exhaustive circuit proof. [P ZIP paths indexed above; R/gold-1286q-fb501d96/generation/prove.py and evidence/admission/formal/ TLC logs.]

W has seven Lean local contracts in its formal README/receipt; not every route stores a separate Z3/TLA file in its local `formal/`. Reused dependencies live in INPUTS/archives. P/U/N/V verification scripts bind source/native operation sequences and theorem interfaces, but **their Python/Rust compilers are not proved Lean compilers**. G epoch11's S2 result is source/native hash and complete-operation agreement plus resource/audit receipts. Its `accepted: true` field denotes that S2 admission, not a Shor certificate. [R/gold-1198q-dd745c8c/formal/README.md; R/gold-1298q-e67e3563/generation/{lower,prove,reproduce}.py; G/notes/epoch11-result.json.]

### Bad events and their probability status

| Family | Bad events | Bound actually established |
|---|---|---|
| 1669→1627→1499/1466/1435/1402/1401 | Inherited `x(P+Q)=Qx`, ordinary-domain equivalent `P=-2Q`; later truncated corrections/comparisons add their own predicates | No-bad trace composition and off-bad equalities. A singleton could have mass `1/order` **if** a caller proved uniform independent P; no such general Shor-call theorem is inherited |
| 1283/1240/1239/1198 | Fixed 270-row nonconvergence, live-width/padding overflow, K2 prefix tie decided below retained prefix, missing reduction near modulus, finite low carry/borrow escape, controlled-add cleanup prefix/equality misclassification, affine exceptions | Conditional algebra/prefix monotonicity and concrete counterexample repair; **no proved uniform probability bound found** |
| 1367/1337/1299/1298/1286 | Signed capacity overflow, schedule nontermination (741/750 etc.), truncated comparison/carry phase, 68/72/other fold-window support, exceptional affine inputs; discarded information can cause phase/ancilla errors | Conditional finite-word/phase/trace lemmas, finite models, source/native agreement and deep shots; **uniform failure bound explicitly open** |
| G epoch11 | Walk-width/horizon tails and finite prefix/fold cells | Model `8.6957122209e-8/add = 7e-8 walk + 1.6957122209e-8 windows`; not Lean-proved, not a certified confidence upper bound |
| exact 2820/2841 | No approximation carve-out declared | No quantitative bad-event bound needed for declared exact arithmetic, but total quantum correctness still unproved |

Sources: each route's `named_bad_events`/contracts.json; F/ApproxReplayBadEvents.lean; D/dist/submission-note.md; G/notes/epoch11-result.json. For Gold1198, correction windows are **128 bits** and minimum K2 prefix **80 bits**, but inherited 32-bit cleanup prefixes and other events remain. For Gold1240, K2 floor **64**, cleanup **32**, add/sub/fused fold widths **60/62/63**. The 32-bit cleanup tie model is an assumption about **correlated reached operands**, not the theorem that a uniformly random 32-bit string matches a fixed string. [R/gold-1198q-dd745c8c/route.json; R/gold-1240q-fef245d4/route.json.]

G's walk model sampled **400,000,000 walks**, with 1 row failure and 13 post-horizon cases, then booked `7e-8` for two walks; its fold76 increment rescales an older model by `(15/255)*(218/193)`. These are useful numerical risk models, not a universal theorem. Gold1240's note explicitly calls the high-prefix tie model **heuristic**. Illustratively, **assuming** at most 1,080 relevant tests each and uniform ties gives `1080*2^-64 + 1080*2^-32 ≈2.515e-7/add`; neither 1,080 as a complete census nor uniform conditional ties is proved here. A clean million-shot test cannot prove a worst-case-in-d channel bound. [G/notes/epoch11-result.json; D/dist/submission-note.md; L/workspace/gold_costs.py.]

The worktree `E/.claude/worktrees/gold-descent-progress-416588/` preserves earlier approximation roadmap/formal-insight notes and the 1240 deep-audit summary in AGENTS. Canonical sealed-route files take precedence over a worktree copy, donor headline or remembered shot count. The roadmap separates exact mechanisms from approximation policies; it does not close the missing probability theorem. [That worktree's `notes/{2026-08-21-approximation-formalization-roadmap,2026-08-21-formal-check-strictness-audit,2026-08-23-point-add-formal-representation-insight-inventory}.md`; E/routes/README.md.]

## 3. Generator to `Straight` and scalable kernel proof

### Input and intermediate representation

Use the **same pinned generative source** as Rust: e.g. N's `source/{arithmetic.py,constants.json}` plus the recipe definitions; P/U use their frozen source archives and profiles; exact2820 uses reviewed block profiles plus explicitly frozen integration. Add a new backend. Do not import generated Rust as the semantic authority. N's existing lowering compiles Python AST into Rust functions/loops and preserves aliases; it is deterministic construction, **not a formal semantics proof**. Rather than first proving all Python and the Rust runtime, reify its arithmetic subset into a typed Lean source language, then prove the shared primitive/loop interpretation. External translation emits source data and the kernel checks its well-typedness and semantics. [R/gold-1298q-e67e3563/{source/arithmetic.py,generation/lower.py,generation/runtime.rs.in}; R/gold-2820q-9619157c/README.md.]

Proposed source nodes: fixed wires/register views; X/CX/CCX/CZ/CCZ; fresh record allocation; single/compound static guards; fixed `seq`/`repeat`/reverse loops; typed field-add/compare/half/divstep/square blocks; lifetime loans with disjointness/known-state contracts. Distinguish **host-static integers**, **protected point bits**, **measurement records**, and **quantum wires** in the types. Reject Q-dependent host branching, unbounded iteration and arbitrary source callbacks. Allocation is a public fixed map plus a proof that each reuse restores its promised state. An external Python builder is allowed to help produce this data, but its assertion/hashes cannot become axioms. [Design; constraints H/ShorECDLP/Challenge/{StraightLine,Template,Contract}.lean; donor runtime has fixed loops and reuse events.]

`Straight` has only `done`, `gate`, `recordGate`, `measure`, indexed by **start/end record cursors**. A measurement adds exactly one record and **always executes**; all histories share the same suffix. Template gates may inspect exactly one protected constant bit. There is no `repeat`, Boolean record expression, writable classical memory, condition stack or arbitrary conditional measurement constructor in the submitted term. Source loops must *denote* finite expansion into `Straight`; source lemmas can reason about the loop structure before that expansion. [H/ShorECDLP/Challenge/{StraightLine,Template}.lean.]

### Lowering details that affect eligibility and cost

| Source operation | Lowering / proof obligation |
|---|---|
| X/CX/CCX | Literal primitive; prove operand distinctness, not just index bounds |
| CZ/CCZ/Z/SWAP | H–CX–H / H–CCX–H / H–X–H / three CX; prove full quantum action, not a phase-dropping Boolean simulation |
| One constant-bit guard | `TemplateGate.whenBit ref value literalGate`; data is fixed independently of Q |
| One earlier outcome guard | `recordGate (Fin start) value literalGate`; cursor shifting/reindexing theorem |
| AND of records, or constant plus record, or nested guard | Compile into scratch Boolean controls, or specialize a proved decomposition. `whenBit` and `recordGate` cannot be nested as constructors. Materialize a record on a clean wire via record-controlled X if needed; use reversible AND/XOR and later clean it. Count extra wires, CCX and records |
| Classical `BitStore0/1/Invert` and arithmetic | These are absent from `Straight`. Symbolically eliminate immutable constant expressions **only where proved expressible by the protected menu/single-bit guards**; otherwise compute reversible Boolean arithmetic on explicit wires, including cleanup. Do not price native classical processing as free |
| Guarded HMR | Prefer a transformed cell that measures unconditionally and proves the disabled target is zero, with fresh outcome ignored/neutralized when disabled. Prove the resulting **instrument** equals the original channel, including the extra independent record and any later use of an effective `guard AND outcome`. Otherwise synthesize a controlled measurement/reset gadget and prove it. No unconditional replacement without that invariant |
| `release`/loan | No physical gate, only if state/phase-cleanliness theorem justifies reuse. Track global label union and temporary measurement-control banks |

These are real issues in the supplied source: N runtime accepts **two guards**, guards HMR, and implements mutable classical `cop`; `source/arithmetic.py`'s classical add/reduce/coordinate code uses that facility. Reading x/y/negX/negY/tripleX from the protected menu can avoid some classical arithmetic. A generic expression of two table bits is not automatically free. Coherent QROM selection makes the selected-coordinate bank a quantum input, even though each table row is classical. [R/gold-1298q-e67e3563/generation/runtime.rs.in, `record`, `measure`, `cop`; source/arithmetic.py around `coordinate`, classical word-add and guards; H/ShorECDLP/Challenge/{Template,PointFields}.lean.]

### Proof structure and evaluation boundary

1. **Cell semantics:** prove one branch's Kraus action on basis states equals a branch scalar times the intended permutation/linear map, with scalar independent of input; squared scalar magnitudes sum to 1. Lift through `CoherentlyImplementsOn`. Gold's Boolean phase lemmas supply the algebra, but resetting and a correct phase bit alone do not prove normalization or absence of record leakage. [H/ShorECDLP/Framework/Quantum/{CoherentRefinement,MeasurementUncompute,TerminalInterference}.lean; P CarryPhysicalCellV1.]
2. **Word induction:** carry/borrow invariants over an arbitrary-width list; support/disjointness, unchanged operands and clean carries. Prove run, count, gate slots, cursor/measurement count and wire-set inclusion together. Match reverse loops by indexed induction, not expansion of 256 copies. [Design; donor ControlledRegisterProvider/MeasuredComparator; B/Challenge/{GidneyAdd,MeasuredStep,MeasuredWrapper,InPlace}.lean.]
3. **Field and walk induction:** canonical/signed representation invariants, full-width correction correctness, prefix predicates and exceptional cases. Prove actual selected walk termination or a quantified bad-support theorem for its exact recurrence. Instantiate every conditional caller. Use source-stage induction over raw walk/replay/checkpoints; the B9 511-round theorem is reusable only for that selected recurrence. [Design; F/BinaryGcdConvergence.lean; V/N/P scope above.]
4. **Lowering preservation:** typed source constructors map to proved cells; sequence/loop theorem composes semantic, cursor and resource contracts. The generator's finite profile/owner table gets checked with small kernel arithmetic or a reflected verifier whose soundness is itself proved. Finite source→native hash agreement remains a regression/provenance check, not a kernel premise. [Design; B/Challenge/{OuterResources,SharedTable,RegisterCorrection}.lean as existing patterns.]
5. **Whole point operation:** prove total group translation on a concrete encoding, with infinity/doubling/inverse and image corrections. Then prove the controlled form or coherent table-selected form, and connect actual Fourier record positions, reset and decoder. [Design; B/Challenge/{BatchCoherent,EndpointCoherent,CertificateAssembly}.lean; H/ShorECDLP/Challenge/Contract.lean.]

**Structural proofs:** disjoint views, support union, cursor arithmetic, loop count recurrences, carry correctness, normalized measured cleanup, recurrence invariants. **Small evaluation:** fixed profile maxima/sums, literal coefficients, finite bit cases, codeword tables and interval inequalities. **Avoid evaluation:** full 2M-nonlinear-gate quantum execution, all 2^512 point inputs, all measurement branches, or one enormous `decide` about an expanded program. Counts should follow a closed recurrence, not a native census imported as a number. The all-enabled gate bound can deliberately overcount unreachable simultaneous guards and remain sound. [Design; actual cost/record interfaces H/ShorECDLP/Challenge/StraightLine.lean and B/Challenge/OuterResources.lean.]

### Term size, recursion and leanchecker

The native streams have **11–64 million serialized operations**, not merely 2M instructions; condition pushes/pops/classical/register operations have different lowering sizes. A flat list of millions of proof steps or one reducible equality of fully expanded `Straight` terms is a replay risk. Existing P3 proof compilation (~555 seconds/~7 GB) and deep-recursion failure in leanchecker are a relevant **different artifact**, not evidence that the Gold cell already fails. [R/gold-1240q-fef245d4/route.json; R/gold-1402q-50ab5c0a/route.json; L/docs/RELATED-WORK.md, P3 review references.]

Proposed implementation: small irreducible **theorem** boundaries per cell/word/stage; continuation-style builders or composition lemmas with polymorphic record cursors; compact fixed profiles; balanced source composition, and no giant final `rfl` that normalizes the entire term. The source may be balanced, but **final Straight is still a linear inductive spine**: chunking declarations does not magically change the checker or eliminate traversal. Benchmark kernel-only replay at 1 cell, 256-bit word, 1k/10k/100k-gate compositions, then one real divstep block before committing to the whole point-add. Record `.olean` size, peak memory, checking wall time and leanchecker recursion. Use no submitted `opaque`, native evaluator axiom or unchecked binary loader. If frozen-data ingestion itself forces full expansion, test that separately from proof checking and treat failure as a blocker requiring a different representation of the same allowed `Straight`, not an increased source option. [Design; H/ShorECDLP/Challenge/StraightLine.lean; L/AGENTS.md; L/docs/RELATED-WORK.md §P3.]

## 4. Where it plugs in and what it might cost

All projections below are **conditional engineering guesses**, not valid candidate bounds. They keep **26 rounds and 54,168 phase T slots/round** to compare with the accepted entrant. Source first-window lookup is separate; there are **28 subsequent additions** (15 left +13 right), while the uniform outer theorem allows **29 window costs** including first lookup. Binary one-control architecture uses **256+208=464 additions**, subject to a fresh semiclassical schedule proof. [B/Challenge/{WindowBody,OuterResources}.lean; B/Window/StreamGateCounts.lean; L/workspace/ecdsafail_tricks_costs.py.]

### (a) Quantum point + coherently table-selected point

Current `batchedWindowCore` is lookup + signed-y correction + placed batch point-add correction + signed-y correction; protected `SharedTable` has **983,040 rows**, exactly the cap. Gold expects quantum P but classical Q. A port must replace its classically processed Q bits by a **coherent read-only coordinate bank**, provide phase-safe dynamic arithmetic for those inputs, restore that bank/address, and prove the actual batched window acts as controlled translation. Existing value-only classical adapters do not supply this theorem. [B/Challenge/{WindowBody,SharedTable}.lean; R/gold-1283q-b9ab2819/formal/lean/Gold1401ClassicalCoordinateAdapter.lean.]

An optimistic support target for 1240 is `1240+512+16=1768` distinct wires: its original two 256-bit input coordinates, a new selected-Q bank and reused address bank. This **omits** infinity/selection/control scratch and any extra bank required to replace native classical memory. The first-window/lookup, sign handling, exceptional repair, record guards, classical arithmetic and resets must all be added. Existing 3,931-reset-label support does not disappear merely by changing the core. A direct first experiment can retain it and count the real union; a compact replacement needs a new allocation/reset proof. [Design; donor runtime initializes live wires 0..511; B/Challenge/WindowBody.lean, `batchedResetWires`; H/ShorECDLP/Framework/Quantum/Adaptive.lean.]

Let `A=h*(7S)` be a future all-input, guard-lowered, controlled/coherent arithmetic budget, and `L + E + I` the per-round lookup, exceptional-repair and other integration costs. Model:

`Tround = 28*A + 54,168 + L + E + I`, `score = Q*26*Tround`.

The following table sets the unpriced `L+E+I` to **zero** to expose scale. `h=2/4` is sensitivity, not a bound established by a compiler.

| Conditional model | Q target | T/round | T/26 | Q×T |
|---|---:|---:|---:|---:|
| 1240 S=2,114,708, h=1, extras=0 | 1,768 | 414,536,936 | 10,777,960,336 | 19,055,433,874,048 |
| Same, h=2 | 1,768 | 829,019,704 | 21,554,512,304 | 38,108,377,753,472 |
| Same, h=4 | 1,768 | 1,657,985,240 | 43,107,616,240 | 76,214,265,512,320 |
| Exact2820: **all 41,431,550 native records charged as CCX**, before compiler/integration | 3,348 | 8,120,637,968 | 211,136,587,168 | 706,885,293,838,464 |

These suggest 19–77× arithmetic-only headroom for a compact 1240-derived window port against **1,471,463,476,298,712**, but do not show approximation can be certified or h is sufficient. Exact2820's loose all-record count is deliberately much larger than its mean and is **not** a submitted upper bound after lowering. A precise native S census is a high-value cheap next task. [Arithmetic: L/workspace/gold_costs.py; baseline L/work-notes/SCOREBOARD.md; source S in R/gold-1240q-fef245d4/route.json; exact operations in R/gold-2820q-9619157c/route.json.]

### (b) Semiclassical one-control-qubit classical-constant addition

Put rows `(2^i,0)` and `(0,2^j)` in the coefficient table. Their values are supplied by the judge, so no submitted term receives Q; **464 rows** suffice for the comparison schedule. Each add is controlled by the reused Fourier qubit, and feedback uses earlier measurement records; prove the semiclassical measurement ordering and decoder law. The current proof of semiclassical inverse Fourier *after* scalar arithmetic does not alone justify interleaving all scalar actions into this new one-qubit schedule. [Design; H/ShorECDLP/Challenge/Template.lean; B/Fourier/Semiclassical.lean; B/Challenge/OuterResources.lean.]

Do not obtain quantum control by blindly controlling every HMR. Given a proved **total** translation Uq, add a 513-bit dummy initialized to encoded infinity, swap P and dummy conditional on c, apply Uq to dummy, swap back, then clear the known encoded q on c=0. For c=1 this updates P; for c=0 only the dummy was translated and its public value can be unloaded. Two banks of 513 Fredkins cost `2*513*7=7182 T/add`; table-bit and c-controlled clears use Clifford gates if directly expressible. This construction requires Uq on **infinity** even when the ordinary arithmetic domain excludes it, and the same branch scalars across control states to prevent measurement-record leakage. [Design; L/workspace/ecdsafail_tricks_costs.py, `controlled_translation_check`; bench total/coherent interfaces in B/Challenge/BatchCoherent.lean.]

For core width q and `A=h*7S` **including the total-add/exception work within q**, support target is `q+513+1`, and `Tround=464*(A+7182)+54168`. The h=1 1240 row does **not** assert the approximate source is already exact or total.

| Conditional model | Q | T/round | T/26 | Q×T |
|---|---:|---:|---:|---:|
| Compact total1240 target, h=1 | 1,754 | 6,871,958,200 | 178,670,913,200 | 313,388,781,752,800 |
| Same, h=2 | 1,754 | 13,740,529,784 | 357,253,774,384 | 626,623,120,269,536 |
| Same, h=4 | 1,754 | 27,477,672,952 | 714,419,496,752 | 1,253,091,797,303,008 |
| 1240 core + **disjoint current singleton correction workspace** | 4,834 | 7,137,930,424 | 185,586,191,024 | 897,123,647,410,016 |
| Exact2820 **all-native-record upper proxy**, compact total-add workspace assumed | 3,334 | 134,573,061,016 | 3,498,899,586,416 | 11,665,331,221,110,944 |

The disjoint correction row uses `1240 core +1 accumulator infinity +2565 endpoint words +512 equality scratch/flag +2 spare/control allowance +513 dummy +1 phase control =4834` wires and adds `16*35826=573216 T/add`, as brief06's conservative existing-repair model. It requires a new semantic bridge to the Gold core's exceptional images; it is a **price for an integration approach**, not a proof those existing corrections fit unchanged. Gold ordinary affine formulas may encode exceptions differently from `exceptionalImage`. [L/workspace/ecdsafail_tricks_costs.py; H/ShorECDLP/Challenge/Template.lean, `exceptionalImage`; B/Challenge/{BatchCost,BatchPlacement}.lean.]

At 26 rounds the complete controlled add must cost less than about **69.54M T at Q=1754**, **36.58M at Q=3334**, or **25.23M at Q=4834** to beat the current entrant, including all overhead. The exact2820 **mean** proxy alone is `7*5,211,740=36,482,180`; even if it equaled the worst case (unproved), at Q3334 this would leave only ~102k T/add before wrapper/exception/classical costs. Thus “start from the exact line” is attractive for proof but gives a much tighter one-qubit economic case than the approximate1240 headline. [L/workspace/gold_costs.py; R/gold-2820q-9619157c/route.json.]

**Rounds and other budgets:** keep 26 only if the new producer re-establishes per-round success ≥0.163 for every nonzero d and the reset/repetition independence argument. A hypothetical p=0.546 would need 6 rounds, but **no such bound for either new producer is established here**. Candidate checks use the actual round layout (26≤56); measurements/gate slots need separate structural counts. Allowing 464 Fourier measurements and Q resets per round gives ~**3,934,953 measurements/add** for Q1754/464 additions, or **65,207,805/add** for Q1768/28 additions, under the official cap. Classical bit count is not measurement count, especially after guarded-HMR lowering. [B/Challenge/OuterResources.lean; H/ShorECDLP/Challenge/{Official,Contract}.lean; L/workspace/gold_costs.py; current repetition bound L/work-notes/HANDOFF.md.]

### Approximation inside the ≥99% proof

There are two sound routes. **Exact hardening:** use full comparisons/corrections and an all-input selected-walk bound, or correct exceptional images explicitly. Recompute Q/T; do not inherit approximate metrics. **Error-certified approximation:** prove agreement on a good subspace for all histories plus a norm/channel-error bound on the **actual Shor input**, uniformly in nonzero d. A uniformly sampled classical point-add shot is not that input, and measurement records can leak coherent information even with right coordinates. [Design; B/Window/StreamInterference.lean; H/ShorECDLP/Framework/Quantum/{CoherentRefinement,TerminalInterference}.lean.]

Existing `streamRawFourierEventMass_ideal_lower` has lower bound `(9/16)*idealMass -147/16384`. It comes from two interference comparisons and an excluded input mass ≤`7/4096`. It does **not** accept an arbitrary empirical “per add error” argument. `Instrument.bornMass_interference` bounds selected mass of ψ+φ between `(3/4)massψ-3massφ` and `(5/4)massψ+5massφ`; `CoherentlyImplementsOn.terminalMass` transports selected mass exactly on supported input. Gold can reuse this machinery only after constructing its good-support/branchwise coherent implementation and proving excluded **mass**, not counting random-shot failures. CoherentReplacement/EndpointCoherent/BatchCoherent provide exact replacement tools, not a generic uniform-noise certificate. [B/Window/StreamInterference.lean; H/ShorECDLP/Framework/Quantum/{TerminalInterference,CoherentReplacement}.lean; B/Challenge/{EndpointCoherent,BatchCoherent}.lean.]

Illustrative error budgeting, **to be proved in Lean if used**:

- p=0.163 at 26 rounds gives 0.990208214125 success. Required p for 26 fresh rounds is `1-.01^(1/26)=0.162322359932`; hence per-round **event-probability loss** can be ≤0.000677640068 if a uniform conditional round bound and valid repetition proof survive. Alternatively a one-shot whole-experiment comparison has only 0.000208214125 slack. These are different proof strategies/budgets.
- If two normalized implementations agree on a common good input subspace of bad initial mass ε, their Stinespring-output distance can be bounded by `2√ε`; event-probability loss ≤`4√ε` is a conservative sufficient estimate, **provided** a common dilation/agreement theorem is established. Then ε≤`2.86998e-8/round` would suffice for the preceding per-round allowance. A union of **initial-space** bad predicates with equal mass budgets would give ~`1.025e-9/add` at 28 calls or `6.185e-11/add` at 464 calls. These are sufficient illustrative targets, not necessary lower bounds or an existing theorem.
- A generic sequential norm-error hybrid instead sums each call's norm error; it may charge `4*sum(sqrt(eps_i))`, not `4*sqrt(sum(eps_i))`. To get the latter stronger form one must prove a common good-trace/input-subspace argument and bound that union on the actual distribution. Correlation, changing reached states and adaptive histories must be handled explicitly. The Gold no-bad logical induction does not supply their measures.
- G's modeled `8.6957e-8/add` would union to `2.4348e-6` or `4.0348e-5/round` at 28/464 calls. Even **if** those became valid classical mass bounds, they do not automatically fit the coherent sufficient target above. Treating bad events as benign decoder rejection would allow linear probability loss only after proving the channel really flags/contains them without harmful interference.

[Calculations: L/workspace/gold_costs.py; logical starting point F/ApproxReplayBadEvents.lean; interference lemmas cited above. No new analytical error theorem was proved in this audit.]

## 5. Recommendation and milestones

**Yes, a Gold-derived certified entrant is realistic as a staged arithmetic/compiler effort. The current artifacts do not justify a delivery promise for a complete low-Q entrant.** Keep the accepted streaming26 baseline. Begin with the exact reusable cells from P/N source, while obtaining a real static census and studying the sealed exact2820 algorithms. The small approximate routes are excellent resource targets and regression sources; their uniform support/failure theorem is the main unresolved mathematical risk. Prefer hardening/conditional-support discharge before claiming a million-shot audit solves that risk. [Evidence and gaps in sections 1–4; L/work-notes/HANDOFF.md.]

| Milestone | Concrete reviewable result / stop condition | Effort **guess**, one experienced Lean engineer |
|---|---|---|
| M0: exact source cell → Straight | Add backend rule for `and_uncompute` or `carry_base_recipe(prev=None)`; emit CCX, one X-measure-reset and record-CZ; prove normalized branch action, source/run correspondence, **7 T, 1 measurement, 4 primitive gate slots, 3 wires**, cursor shift and WF; replay with leanchecker on bench-compatible 4.28 in a scratch project outside H | 1–3 working days if reusing bench MBU; longer if proof-port friction |
| M1: parametric exact word | Source-bound `chunk_add`/measured comparator, all widths/outcomes, operand preservation, clean reuse, structural count/support/record lemmas; 256-bit kernel replay with measured memory/time | 1–2 weeks |
| M2: real walk block + scaling test | One exact field correction or divstep block; source profile/physical-wire proof; 100k-gate replay experiment; static count + guarded measurement/classical-control lowering | 2–6 further weeks; stop whole-route work if replay or width premises cannot be controlled |
| M3: point-add + one-control round | Total or precisely supported affine channel, exceptional corrections, explicit all-cost/all-label bounds; actual semiclassical/window interface and decoder-position theorem | months plausible; no reliable date until M2 |
| M4: full Certificate | Uniform nonzero-d success ≥99%, all budgets, allowed axioms and official kernel replay; new score/snapshot | depends chiefly on support/error proof, not generation throughput |

M0 program schematic at start cursor s, distinct a,b,t and t initially zero:

```text
gate (literal (CCX a b t))
measure t
recordGate (last outcome : Fin (s+1)) true (H b)
recordGate (last outcome : Fin (s+1)) true (CX a b)
recordGate (last outcome : Fin (s+1)) true (H b)
done
```

The three conditional Clifford gates are CZ repair; each branch's Kraus map should equal `1/√2` times identity on the a,b state and t=0. This proves coherence on arbitrary superpositions, not just eight bit tests. Four gate slots are a CCX plus three CZ-lowering slots; measurement is counted separately by cursor difference. A symbolic Python phase check is included in `gold_costs.py` and passes all bits/outcomes, **but no Lean version of M0 is claimed here**. A follow-on source-bound n-bit add without output carry should recover `n-1` computed carries/measurements and `7(n-1)` T under the source's layout and cleanup premises. [R/gold-1298q-e67e3563/source/arithmetic.py, `and_uncompute`, `carry_base_recipe`, `chunk_add`; H/ShorECDLP/Challenge/StraightLine.lean; H/ShorECDLP/Framework/Quantum/MeasurementUncompute.lean.]

For M0/M1, source identity matters: emit from the pinned recipe/IR and bind the theorem to that generated `Straight`, rather than proving a manually similar circuit. Check Lean source axioms and **kernel-only replay** from the first milestone. This is the smallest result that demonstrates the source→allowed-data→quantum-semantics→resource-proof pipeline, while leaving the expensive whole-point and success arguments explicitly open. [Design; P3 failure discussion in L/docs/RELATED-WORK.md; H/ShorECDLP/Challenge/{StraightLine,Contract}.lean.]
