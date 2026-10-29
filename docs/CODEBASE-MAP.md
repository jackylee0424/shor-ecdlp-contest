# Bench codebase map

Source audit: bench `/home/gitzard/shorecdlp`, HEAD `535a493`, 2026-10-29. Paths below are relative to the bench; every listed `.lean` path is an importable module. Each line gives its role and useful public declarations (names are relative to the namespace opened by that module). The numeric path component is escaped in Lean: `import ShorECDLP.Submission.«2607_13816».Submission`.

`Math` is pure mathematics; `Framework` supplies neutral machine semantics. Naive and 2607_13816 are isolated implementations; their internal import policy forbids cross-imports. Entrant currently reuses Naive. Entrant can import protected libraries but can edit only its own directory. Start at `Entrant/Main.lean` for the shipped certificate, `Naive/Challenge/NumericCertificate.lean` for the original protected baseline, or `2607_13816/Submission.lean` for the legacy paper contracts. The latter do **not** supply the protected challenge certificate; migration lives under that submission's `Challenge/` directory.

This map covers the main APIs, arithmetic engines, complete streaming proof chain and every migration module. Low-level EEA bit/interval/packing proofs and auxiliary primitive-count refinements are reached through their listed production modules rather than individually catalogued. `All.lean` files aggregate imports, not additional certificates.

Read alongside [BASELINE-BREAKDOWN.md](BASELINE-BREAKDOWN.md). Bench planning material read: `docs/PLAN.md` headings; all `docs/NAIVE_*.md` and `docs/STREAMING_*.md`; `Submission/2607_13816/INTEGRATION.md` and `REFERENCE.md`. PLAN and early incremental NAIVE notes retain historical unfinished claims and obsolete numeric snapshots. Prefer current theorem statements and the later numeric/integration handoffs.

## Challenge: protected contract

- `ShorECDLP/Challenge/Contract.lean` — Protected success/resource contract and final public-point verification — `Certificate`, `Bounds`, `Limits`, `verifiedCandidate`, `declaredScore`.
- `ShorECDLP/Challenge/Decoder.lean` — Protected nearestPair/wrappedShift candidate enumeration and transcript reads — `DecodeLayout`, `DecoderParams`, `TrialPositions`, `candidates`, `readWord`.
- `ShorECDLP/Challenge/DecoderSmoke.lean` — Small elaboration/contract smoke examples; not an arithmetic implementation — `baselineParams`.
- `ShorECDLP/Challenge/ExtendedContract.lean` — Optional extended resource certificate and conversion from the basic contract — `ExtendedBounds`, `ExtendedCertificate`, `Certificate.extend`.
- `ShorECDLP/Challenge/Official.lean` — Organizer admission limits — `officialLimits`.
- `ShorECDLP/Challenge/PointFields.lean` — Protected point fields including exceptional-point transforms — `exceptionalImage_self`, `exceptionalDenominator_ne_zero`, `doubledCoordinates_eq`.
- `ShorECDLP/Challenge/Resources.lean` — Protected qubits, abstract T, measurement and extended gate metrics — `Resources`, `resources`, `Resources.score`.
- `ShorECDLP/Challenge/Smoke.lean` — Small elaboration/contract smoke examples; not an arithmetic implementation — import-only/example module (no public API).
- `ShorECDLP/Challenge/StraightLine.lean` — Fixed straight-line syntax, cursor-indexed measurement references and evaluator — `Straight`, `StraightEntry`, `Straight.instantiate`, `Straight.WellFormed`, `Straight.gateSlots`.
- `ShorECDLP/Challenge/StraightSmoke.lean` — Small elaboration/contract smoke examples; not an arithmetic implementation — `sample`.
- `ShorECDLP/Challenge/Template.lean` — Fixed coefficient rows, protected field bits and optional constant-controlled slots — `PointCoeff`, `PointField`, `ConstantBit`, `TemplateGate`, `readConstant`.

## Framework: shared semantics

- `ShorECDLP/Framework/BasisState.lean` — Boolean wire states, register values, updates and clean-wire predicates — `BasisState`, `zeroBasisState`, `Clean`, `regValue`.
- `ShorECDLP/Framework/Classical/Semantics.lean` — Classical action of reversible gate lists and the HP-free circuit predicate — `applyGate`, `run`, `run_append`, `HPFree`.
- `ShorECDLP/Framework/CostModel.lean` — Distinct-wire counting and abstract T cost with adjoint/composition rules — `circuitWires`, `qubitCount`, `tCost`, `tCount`.
- `ShorECDLP/Framework/InstructionSet.lean` — Primitive gates, phase direction, adjoints and wire well-formedness — `Wire`, `Gate`, `Circuit`, `CircuitWellFormed`.
- `ShorECDLP/Framework/Quantum/Adaptive.lean` — Measurement/reset circuit syntax and finite Kraus-branch instruments — `AdaptiveCircuit`, `Instrument`, `InstrumentBranch`, `run_bornMass_eq_one`.
- `ShorECDLP/Framework/Quantum/AdaptiveComposition.lean` — Associativity of physical adaptive sequencing — `circuit_seq_done`, `circuit_seq_assoc`.
- `ShorECDLP/Framework/Quantum/AdaptiveDisjoint.lean` — Commutation of adaptive branches with disjoint phase/reset operations — `AdaptiveCircuit.branch_commute`, `AdaptiveCircuit.branch_P_commute`.
- `ShorECDLP/Framework/Quantum/AdaptiveFrame.lean` — Preservation of wires outside an adaptive circuit's support — `AdaptiveCircuit.branch_frame`.
- `ShorECDLP/Framework/Quantum/AdaptiveHadamard.lean` — Move disjoint Hadamard preparation across adaptive arithmetic — `AdaptiveCircuit.branch_H_commute`, `AdaptiveCircuit.prepare_hadamards_run`.
- `ShorECDLP/Framework/Quantum/AdaptiveMeasurement.lean` — Measurement/reset followed by recorded correction and coherent implementation — `measureResetThen`, `measureResetThen_coherent`.
- `ShorECDLP/Framework/Quantum/CleanRelabel.lean` — Transport clean-state premises through physical wire permutations — `relabelBasis_clean`, `relabelState_clean`, `branch_relabel_clean`.
- `ShorECDLP/Framework/Quantum/CoherentRefinement.lean` — Transcript-independent coherent implementation on a valid input subspace — `SupportedOn`, `CoherentlyImplementsOn`, `coherent_final_probability_eq`.
- `ShorECDLP/Framework/Quantum/CoherentReplacement.lean` — Replace an ideal/unitary component inside a coherent implementation — `cancelUnitaryRight`, `replaceInitialUnitary`.
- `ShorECDLP/Framework/Quantum/InnerProduct.lean` — Inner product, norm preservation and inverse-circuit cancellation — `inner`, `normSq_run_ket`, `run_run_adjoint`.
- `ShorECDLP/Framework/Quantum/Interference.lean` — Event-mass interference bounds for good/bad input components — `Instrument.eventMass`, `normSq_mapDomain`, `normSq_neg`, `CoherentlyImplementsOn.eventMass`.
- `ShorECDLP/Framework/Quantum/Measurement.lean` — Joint register probabilities and normalization — `jointRegisterProbability`, `jointRegisterProbability_sum_eq_normSq`.
- `ShorECDLP/Framework/Quantum/MeasurementUncompute.lean` — X-measure/reset with Z/CZ and recomputation corrections — `pauliZ`, `controlledZ`, `recomputeMeasurementUncompute_coherent`.
- `ShorECDLP/Framework/Quantum/Relabel.lean` — Wire-permutation transport of states, circuits, branches and costs — `relabelBasis`, `relabelState`, `AdaptiveCircuit.relabel_qubitCount`.
- `ShorECDLP/Framework/Quantum/RelabelCongr.lean` — Composition and support-congruence laws for wire relabeling — `Gate.relabel_congr`, `AdaptiveCircuit.relabel_trans`, `AdaptiveCircuit.relabel_congr`.
- `ShorECDLP/Framework/Quantum/Semantics.lean` — Finite-support complex quantum states and linear unitary execution — `State`, `ket`, `applyGate`, `run`, `run_ket_agrees_classical`.
- `ShorECDLP/Framework/Quantum/TerminalInterference.lean` — Interference comparison through a final instrument and selected event — `Instrument.bornMass_neg`, `Instrument.seq_bornMass_le`, `CoherentlyImplementsOn.terminalMass`.
- `ShorECDLP/Framework/Repetition.lean` — Pure independent-retry probability and sequential T arithmetic — `independentRetrySuccessProbability`, `repeatedTCount`.

## Math: pure field, curve and recovery results

- `ShorECDLP/Math/All.lean` — Aggregate imports for this layer; prefer a narrower module when iterating — import-only/example module (no public API).
- `ShorECDLP/Math/Bitcoin.lean` — Pure nearest-numerator and scalar recovery postprocessing — `nearestNumerator`, `orderFindingPostprocess`.
- `ShorECDLP/Math/BitcoinCurve.lean` — secp256k1 field/order constants, affine curve, generator and point coordinates — `p`, `order`, `Fp`, `Point`, `G`, `G_ne_zero`.
- `ShorECDLP/Math/BitcoinPrimes.lean` — Kernel-checkable primality results for the field and subgroup order — `p_prime`, `order_prime`.
- `ShorECDLP/Math/Correctness/Reduction.lean` — Hidden-subgroup pairing and discrete-log recovery algebra — `oracleExponent`, `annihilatesPeriod_iff`, `recoverShift_correct`.
- `ShorECDLP/Math/CyclicCharacters.lean` — Cyclic character orthogonality and uniform point-eigenstate sums — `character_sum`, `eigenvalue_add`.
- `ShorECDLP/Math/EllipticCurve/AffineFormula.lean` — Total mathematical affine addition, generic and doubling identities — `affineAdd`, `affineAdd_correct`, `affineAdd_generic`, `affineAdd_doubling`.
- `ShorECDLP/Math/EllipticCurve/GeneratorOrder.lean` — Generator scalar-order certificate — `generator_nsmul_eq_zero`, `generator_order`.
- `ShorECDLP/Math/EllipticCurve/Precompute.lean` — Pure doubling tables used by binary scalar multiplication — `doublingTable`, `doublingTable_get`, `doublingTable_adjacent`.
- `ShorECDLP/Math/Field.lean` — Fermat inversion identity over a prime field — `fermat_inv`.
- `ShorECDLP/Math/PhaseApproximation.lean` — Nearest phase, circular distance and geometric-sum lower bounds — `eigenvalue`, `circularDistance`, `geometric_phase_average_lower_bound`.

## Entrant: shipped editable implementation

- `ShorECDLP/Submission/Entrant/Main.lean` — Shipped one-trial protected entry, decoder and complete official certificate — `entry`, `layout`, `bounds`, `certificate`.
- `ShorECDLP/Submission/Entrant/Success.lean` — Transfer phase-window mass into the ECDLP recovery event — `success_of_window_mass`, `postprocess_of_windows`.
- `ShorECDLP/Submission/Entrant/Trial.lean` — 265-bit layout, 530 fixed coefficients, compiled trial and resource bounds — `entryE`, `entryE_qubits`, `templateT_trialE`, `entryE_tModel`, `entryE_measurements`.
- `ShorECDLP/Submission/Entrant/WindowMass.lean` — Analytic mass bound for the wider phase windows — `window_mass`, `ampSq`.

## Naive: arithmetic and point/scalar circuits

- `ShorECDLP/Submission/Naive/Arithmetic/Adder.lean` — Five-wire reversible full adder with three CCX gates — `fullAdder`, `fullAdder_tCount`.
- `ShorECDLP/Submission/Naive/Arithmetic/Contracts.lean` — Register layouts, support/cleanliness and arithmetic correctness/resource interfaces — `RegisterLayout`, `ModAddContract`, `ModSubContract`, `ModMulContract`, `ModExpContract`.
- `ShorECDLP/Submission/Naive/Arithmetic/Controlled_PointAdd.lean` — Clean controlled constant-point addition, out-of-place then in-place — `controlledPointAdd`, `controlledPointAddWork`, `controlledPointAdd_tCount_of_ne_zero`.
- `ShorECDLP/Submission/Naive/Arithmetic/FermatInv.lean` — Specialize modular exponentiation correctness to prime-field inversion — `correct`.
- `ShorECDLP/Submission/Naive/Arithmetic/InPlaceAdder.lean` — Cuccaro add with reusable carry and explicit carry output — `inPlaceAddCarry`, `inPlaceAddCarry_correct`, `inPlaceAddCarry_tCount`.
- `ShorECDLP/Submission/Naive/Arithmetic/InPlaceModular.lean` — In-place subtraction/comparison, modular reduction/doubling and controlled addition — `reduceWithFlag`, `modularDouble`, `controlledModAdd`, `controlledModAdd_tCount`.
- `ShorECDLP/Submission/Naive/Arithmetic/LowSpaceModMul.lean` — Reused-workspace MSB-first Horner multiplier used by the shipped entrant — `horner`, `program`, `program_tCount`, `modMul_contract`.
- `ShorECDLP/Submission/Naive/Arithmetic/ModAdd.lean` — Clean out-of-place modular addition by two ripples and selection — `modAdd`, `modAddCompute_tCount`, `modAdd_tCount`, `modAdd_contract`.
- `ShorECDLP/Submission/Naive/Arithmetic/ModExp.lean` — Generic reversible square/multiply schedule with stored intermediate registers — `Plan`, `Schedule`, `Plan.program`, `Plan.cost`.
- `ShorECDLP/Submission/Naive/Arithmetic/ModMul.lean` — Older history-based schoolbook multiplier, retained separately from LowSpaceModMul — `Plan`, `program_correct`, `modMul_contract`.
- `ShorECDLP/Submission/Naive/Arithmetic/ModSub.lean` — Clean modular subtraction with complemented input and conditional correction — `modSub`, `modSubCompute_tCount`, `modSub_tCount`.
- `ShorECDLP/Submission/Naive/Arithmetic/PointAdd.lean` — Total affine addition/doubling, branch selection, field wrappers and shared workspace — `pointAdd`, `pointAddWork`, `pointAddFiniteCompute_tCount`, `pointAdd_finite_tCount`, `pointAdd_correct`.
- `ShorECDLP/Submission/Naive/Arithmetic/Predicates.lean` — Clean zero/equality flags with reversible conjunction histories — `zeroFlag`, `equalFlag`, `equalFlag_tCount`.
- `ShorECDLP/Submission/Naive/Arithmetic/Primitives.lean` — Constant loads, register copies and controlled word selection — `loadConst`, `copyReg`, `selectPoint`, `selectPoint_tCount`.
- `ShorECDLP/Submission/Naive/Arithmetic/RippleAdder.lean` — Out-of-place ripple chain and its exact 21n T count — `ripple`, `ripple_correct`, `ripple_tCount`.
- `ShorECDLP/Submission/Naive/Arithmetic/ScalarMul.lean` — Binary controlled translations using precomputed doubling-table constants — `scalarMul`, `scalarMulCore`, `scalarMulWork`, `scalarMul_correct`.
- `ShorECDLP/Submission/Naive/Arithmetic/Secp256k1Instance.lean` — Concrete width-257 add/multiply/exponentiate engines and Fermat specialization — `secpAddProgram_tCount`, `secpMulProgram_tCount`, `secpProgram_tCount`, `historyCount_eq`, `secp_fermat_inverse`.

## Naive: protected challenge implementation

- `ShorECDLP/Submission/Naive/Challenge/Certificate.lean` — Protected nearestPair recovery and symbolic repeated-entry certificate — `repeatedDecodeLayout`, `naiveRepeatedEntry_verified_success`, `naiveRepeatedEntry_certificate`.
- `ShorECDLP/Submission/Naive/Challenge/Constants.lean` — Compile protected constant-field loads and subtraction into template slots — `fieldLoadGates`, `fieldSubConstGates`, `constantGateProgram`.
- `ShorECDLP/Submission/Naive/Challenge/ExtendedCertificate.lean` — Optional extended-gate bounds for the completed Naive entry — `naiveExtendedBounds`, `naiveRepeatedEntry_extended_certificate`.
- `ShorECDLP/Submission/Naive/Challenge/FixedReset.lean` — Q-independent dense reset list and fixed transcript stride — `fixedResetWires`, `fixedRepeated`, `fixedRepeated_success`.
- `ShorECDLP/Submission/Naive/Challenge/NumericCertificate.lean` — Closed numeric protected certificate for the 26-round Naive entry — `naiveNumericBounds`, `naiveRepeatedEntry_numeric_certificate`.
- `ShorECDLP/Submission/Naive/Challenge/NumericCosts.lean` — Static template T formulas from field loads through controlled points and repetition — `controlledPoint_templateT`, `scalarGates_templateT`, `templateT_trial`, `straightT_repeated`.
- `ShorECDLP/Submission/Naive/Challenge/NumericLengths.lean` — Conservative syntax-slot bounds composed without expanding enormous circuits — `controlledPointGates_length_le`, `naiveRepeatedEntry_gateSlots_le`.
- `ShorECDLP/Submission/Naive/Challenge/NumericQubits.lean` — Uniform fixed support and 206624-wire bound for arbitrary public inputs — `trialGates_fixed_support`, `naiveRepeatedEntry_qubit_bound`.
- `ShorECDLP/Submission/Naive/Challenge/Physical.lean` — Bridge original unitary probability into observed/reset adaptive trials — `naiveObserved`, `naiveRepeated_success`.
- `ShorECDLP/Submission/Naive/Challenge/PointGates.lean` — Compile total controlled point addition and fixed powers-of-G/Q coefficient rows — `controlledPointGates`, `naivePowerTable`, `dlogPoint_order`.
- `ShorECDLP/Submission/Naive/Challenge/Probability.lean` — Recorded pair events, observation mass and trial normalization — `pairEvent`, `observedTrial`, `observedTrial_recordMass`.
- `ShorECDLP/Submission/Naive/Challenge/Readout.lean` — Z readout using H, X-measure/reset and recorded X restoration — `observeWires`, `zObserve`, `observeWires_jointProbability`.
- `ShorECDLP/Submission/Naive/Challenge/RecordPositions.lean` — Bind absolute transcript offsets to protected little-endian decoder reads — `readWord_range`, `repeatedTrialPositions`, `fixedRepeatedSuccess_actualWords`.
- `ShorECDLP/Submission/Naive/Challenge/RepeatedEntry.lean` — Fixed 26-round StraightEntry, including readout and reset — `naiveRepeatedEntry`, `roundProgram`, `repeatedProgram`, `repeatedStaticBounds`.
- `ShorECDLP/Submission/Naive/Challenge/ResetRepeat.lean` — Physical reset to zero and actual sequential-instrument retry probability — `resetTrial`, `repeatFixed`, `resetTrial_twentySix`.
- `ShorECDLP/Submission/Naive/Challenge/Static.lean` — Well-formedness of every template slot, including inactive constants — `trialProgram_wellFormed`, `observedTrialProgram_wellFormed`.
- `ShorECDLP/Submission/Naive/Challenge/StaticResources.lean` — Static wire/T bounds over syntax, valid for every read/history — `straightWires`, `straightT`, `straight_t_bound`, `observedTrialProgram_resources`.
- `ShorECDLP/Submission/Naive/Challenge/TrialGates.lean` — Compose H, two scalar programs and inverse QFT into one fixed trial — `scalarGates`, `trialGates`, `observedTrialProgram`, `observedTrialProgram_run`.

## Naive: oracle, Fourier and success proof

- `ShorECDLP/Submission/Naive/All.lean` — Aggregate imports for this layer; prefer a narrower module when iterating — import-only/example module (no public API).
- `ShorECDLP/Submission/Naive/Contract.lean` — Original concrete Bitcoin unitary-submission record — `BitcoinECDLPSubmission`.
- `ShorECDLP/Submission/Naive/Correctness/EndToEnd.lean` — Concrete original success/resource proof and dense Bitcoin wire allocation — `bitcoinAReg`, `bitcoinPointReg`, `bitcoinWireLayout`, `bitcoinECDLPTrial_fixed_support`.
- `ShorECDLP/Submission/Naive/Correctness/Trial.lean` — Unitary H/oracle/IQFT ECDLP trial and execution equation — `ecdlpTrial`, `ecdlpTrial_run`.
- `ShorECDLP/Submission/Naive/EllipticCurve/ECDLPOracle.lean` — Two scalar additions implementing (a,b,R) ↦ R+aG+bQ — `ecdlpOracle`, `ecdlpOracle_correct`, `ecdlpOracle_spec`.
- `ShorECDLP/Submission/Naive/EllipticCurve/PointEncoding.lean` — Injective 513-bit affine encoding with finite tag and zero encoding infinity — `pointWidth`, `encode`, `pointEncoding`.
- `ShorECDLP/Submission/Naive/EllipticCurve/PointRegister.lean` — Tag/x/y slices and coordinate padding/write identities — `tag`, `x`, `y`, `slices_write_some`.
- `ShorECDLP/Submission/Naive/EllipticCurve/Secp256k1.lean` — Compatibility import of the pure mathematical curve layer — import-only/example module (no public API).
- `ShorECDLP/Submission/Naive/OrderFinding/Defs.lean` — Two-register order-finding program, success event and clean setup interface — `orderFinding`, `ECDLPSetting`, `OrderFindingSetup`.
- `ShorECDLP/Submission/Naive/OrderFinding/Main.lean` — Aggregate order-finding correctness theorem — `orderFinding_correct`.
- `ShorECDLP/Submission/Naive/OrderFinding/OracleRefinement.lean` — Refine a concrete clean circuit into the quantum oracle specification — `ofCircuit`.
- `ShorECDLP/Submission/Naive/OrderFinding/OracleSpec.lean` — Encoded group oracle's coherent specification — `PointEncoding`, `ECDLPOracleSpec`.
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Defs.lean` — Hadamards, phase-estimation syntax and controlled-power assumptions — `hadamards`, `phaseEstimation`, `ControlledPowersOn`.
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Main.lean` — Exact and approximate quantum phase-estimation correctness — `phaseEstimation_correct_exact`, `phaseEstimation_correct_approx`.
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Proofs/Approximations.lean` — Compatibility import of pure phase-approximation results — import-only/example module (no public API).
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Proofs/ControlledPowers.lean` — Uniform eigenstate action of controlled powers — `controlledPowers_uniform_eigenstate`.
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Proofs/Eigenphase.lean` — Eigenvalue powers and exact Fourier phase agreement — `eigenvalue_exact_pow_eq_qftPhase`.
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Proofs/Fourier.lean` — Phase-kicked state, inverse Fourier amplitudes and geometric sums — `qpeAmplitude`, `run_iqft_kicked_phase_state`.
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Proofs/Hadamard.lean` — Uniform register preparation on a clean input — `run_hadamards_clean`.
- `ShorECDLP/Submission/Naive/OrderFinding/PhaseEstimation/Proofs/Probability.lean` — Register probabilities of label-state superpositions — `registerProbability_label_superposition`.
- `ShorECDLP/Submission/Naive/OrderFinding/Proofs/CyclicEigenstates.lean` — Point-register cyclic eigenbasis and orthonormality — `pointEigenstate`, `pointEigenstate_orthonormal`, `ket_eq_pointEigenstate_average`.
- `ShorECDLP/Submission/Naive/OrderFinding/Proofs/FourierSampling.lean` — Full two-dimensional order-finding Fourier-state equality — `orderFinding_eq_fourierState`.
- `ShorECDLP/Submission/Naive/OrderFinding/Proofs/OracleKickback.lean` — Group-translation eigenstate phase kickback — `oracle_pointEigenstate_kickback`.
- `ShorECDLP/Submission/Naive/OrderFinding/Proofs/Postprocess.lean` — Recover the scalar from character peaks and nearest phases — `orderFindingPostprocess_of_character_peak`.
- `ShorECDLP/Submission/Naive/OrderFinding/Proofs/Probability.lean` — Joint output probability as the cyclic-character average — `jointRegisterProbability_orderFinding_eq_character_average`.
- `ShorECDLP/Submission/Naive/OrderFinding/Proofs/SuccessProbability.lean` — Lower bound by the nonzero-character peak sum — `nonzero_character_peak_sum_le_success`.
- `ShorECDLP/Submission/Naive/QFT/Defs.lean` — Coherent controlled-phase QFT, bit reversal and adjoint IQFT — `cPhase`, `qft`, `iqft`.
- `ShorECDLP/Submission/Naive/QFT/Main.lean` — Fourier semantics and QFT/IQFT cancellation — `qft_correct`, `iqft_correct`, `iqft_qft_cancel`.
- `ShorECDLP/Submission/Naive/QFT/Proofs/CPhase.lean` — Clean-ancilla controlled-phase semantics and 15-T accounting — `run_cPhase_ket`, `tCount_cPhase`.
- `ShorECDLP/Submission/Naive/QFT/Proofs/Count.lean` — Exact 15·n(n−1)/2 QFT cost and physical validity — `tCount_qft`, `tCount_iqft`, `iqft_wellFormed`.
- `ShorECDLP/Submission/Naive/QFT/Proofs/Fourier.lean` — Basis-state Fourier transform semantics — `fourierState`, `run_qft_ket`.
- `ShorECDLP/Submission/Naive/QFT/Proofs/Step.lean` — Controlled-phase layer and one QFT-step semantics — `run_qftStep_ket_exp`.
- `ShorECDLP/Submission/Naive/QFT/Proofs/Swap.lean` — Three-CX SWAP semantics and zero T cost — `run_swap_ket`, `tCount_swap`.
- `ShorECDLP/Submission/Naive/Submission.lean` — Completed original Bitcoin implementation export — `bitcoinECDLPSubmission`.

## 2607_13816: exports

- `ShorECDLP/Submission/2607_13816/All.lean` — Aggregate imports for this layer; prefer a narrower module when iterating — import-only/example module (no public API).
- `ShorECDLP/Submission/2607_13816/Contract.lean` — Original full-precision windowed ECDLP contract — `SecpWindowContract`, `secpWindowContract`.
- `ShorECDLP/Submission/2607_13816/DirectContract.lean` — Direct-first-lookup windowed ECDLP contract — `DirectSecpWindowContract`, `directSecpWindowContract`.
- `ShorECDLP/Submission/2607_13816/Submission.lean` — Legacy raw/streaming algorithm exports, success, gate and tight-support contracts — `tight_certificate`, `tight_resources`, `trial_certificate`.

## 2607_13816: field and total point arithmetic

- `ShorECDLP/Submission/2607_13816/Arithmetic/ConstantCompare.lean` — Constant less-than comparator built from Gidney primitives — `controlledGidneyCompareLT`, `controlledGidneyCompareLT_branch_correct`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/ConstantModular.lean` — Controlled/uncontrolled constant modular addition — `controlledConstantModularAdd`, `constantModularAddIdealState_correct`, `controlledConstantModularAdd_branch_correct`, `secp256k1ControlledIncrement_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/ConstantModularCoherent.lean` — Coherent correctness of constant modular addition — `ConstantModularValid`, `controlledConstantModularAdd_coherent`, `uncontrolledConstantModularAdd_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/Doubling.lean` — Modular doubling and reusable-wire rotation implementation — `doublingRotate`, `doublingShift_counts`, `doublingFour_counts`, `secp256k1ModularDouble_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/FiniteCorrection.lean` — Finite matching permutation for repairing exceptional inputs — `finiteMatchingPermutation`, `finiteMatchingPermutation_correct`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/GidneyAdd.lean` — Controlled constant Gidney addition, cleanup and source annotations — `gidneyAddCarryCell`, `gidneyAddIdealState_correct`, `secp256k1GidneyAdd_correct_resources`, `gidneyUncontrolledAddIdealState_correct`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/GidneyCarry.lean` — Measurement-assisted carry primitive and recorded phase cancellation — `gidneyRecordedPhase`, `gidneyGateCount_tCount`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/GidneyCompare.lean` — Controlled comparison with measured carry erasure — `gidneyCompareCarryCell`, `controlledGidneyCompareCarry_branch_correct`, `controlledGidneyCompareGE_branch_correct`, `secp256k1GidneyCompare_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/Halving.lean` — Modular halving inverse and resource formulas — `modularHalve`, `modularHalve_branch_correct`, `secp256k1ModularHalve_counts`, `secp256k1ModularHalve_after_double_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/HornerCoherent.lean` — Coherent forward/inverse Horner multiplication — `HornerInputValid`, `hornerMul_coherent`, `hornerMulInverse_coherent`, `hornerMul_forward_inverse_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/HornerInverse.lean` — Inverse Horner multiplier and cleanup — `hornerMulInverse`, `secp256k1HornerMulInverse_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/HornerMul.lean` — Adaptive Horner multiply-to-zero with clean work — `hornerMul`, `hornerAdd_counts`, `hornerDouble_counts`, `secp256k1HornerMul_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/InPlace.lean` — Figure-15 measured in-place division/multiplication — `fig15MultiplyToWork`, `fig15SwapOutput_run`, `secp256k1InPlaceDivision_coherent`, `secp256k1InPlaceMultiplication_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/InPlaceResources.lean` — T/measurement bounds of the actual in-place arithmetic — `secp256k1InPlaceDivision_T`, `secp256k1InPlaceMultiplication_T`, `secp256k1MeasuredEEAForwardWrapper_tCount`, `secp256k1MeasuredEEAForwardWrapper_measurementCount`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/InPlaceSupport.lean` — Shared physical support and in-place arithmetic certificates — `secp256k1InPlaceDivision_certificate`, `secp256k1InPlaceMultiplication_certificate`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/ModularAdd.lean` — Controlled modular word addition and field-width specialization — `controlledModularAdd`, `controlledModularAdd_branch_correct`, `secp256k1ModularCompare_counts`, `secp256k1ModularAdd_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/ModularNegate.lean` — Controlled modular negation and coherent valid-domain theorem — `modularNegateIdealState`, `modularNegateIdealState_correct`, `controlledModularNegate_branch_correct`, `controlledModularNegate_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/ModularSub.lean` — Controlled modular subtraction and inverse-of-add interface — `controlledModularSub`, `controlledModularSub_branch_correct`, `secp256k1ModularSub_counts`, `secp256k1ModularSub_after_add_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointCircuit.lean` — Figure-14 affine coordinate circuit and coherent refinement — `fig14CoordinateProgram`, `fig14CoordinateProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointCorrection.lean` — Executable exception list and correction matching — `fig14PointEncoding`, `fig14CorrectionSwaps_correct`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointCorrectionCircuit.lean` — Classical correction circuit with cleanup and ket semantics — `pointCorrectionCircuit`, `pointCorrectionCircuit_correct`, `pointCorrectionCircuit_tCount`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointCorrectionPrimitiveCounts.lean` — Primitive counts including complete exceptional repair — `pointWordEdgePrimitives`, `pointWordProgram_primitive_exact`, `pointCorrectionCircuit_primitive_exact`, `totalPointProgram_primitive_exact`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointExceptions.lean` — Finite exceptional set and nonzero-factor lemmas — `fig14ExceptionalPoints`, `fig14ExceptionalPoints_card_le`, `fig14_nonexceptional_factors`, `fig14CoordinateState_nonexceptional`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointGeneric.lean` — Coordinate result on the generic nonexceptional point domain — `fig14CoordinateValues_generic`, `fig14RawDomain_of_factors`, `fig14CoordinateState_generic`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointPermutation.lean` — Coordinate permutation injectivity used for finite repair — `fig14CoordinateEquiv`, `fig14CoordinateValues_equiv`, `fig14CoordinateState_equiv`, `fig14CoordinateState_injectiveOn`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointPrimitiveCounts.lean` — Exact six-component primitive vector for coordinate arithmetic — `pointConstantPrimitives`, `squareSubtract256_secp_primitive_exact`, `fig14SquareSubtract_primitive_exact`, `fig14CoordinateProgram_primitive_exact`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointRawDomain.lean` — Actual raw coordinate program on its explicit nonzero domain — `fig14BeforeDivision`, `fig14RawProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointResourceCounts.lean` — Aggregate point-coordinate and total-point T/measurement formulas — `pointCoordinateT`, `fig14CoordinateProgram_counts`, `totalPointProgram_counts`, `pointAddProgram_counts`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointSupport.lean` — Shared support and complete point-add certificate — `pointAddProgram_certificate`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointTotal.lean` — Canonical pointWrite interface and total controlled group addition — `pointWrite`, `totalPointState_correct`, `pointAddState_correct`, `pointAddProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointTotalCircuit.lean` — Total coordinate-plus-correction circuit with coherent correctness — `totalPointProgram`, `totalPointProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PointWordProgram.lean` — Compile exceptional transpositions through Gray-word edges — `pointWordProgram`, `pointWordProgram_correct`, `pointWordProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/PrimitiveResources.lean` — Primitive gate/resource vector and conversion to the abstract T model — `PrimitiveResources`, `primitiveResources`, `primitiveResources_T_le`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/SourceCorrections.lean` — Correction-annotated program vocabulary and erasure — `CorrectionFragment`, `correctionResetThen_erase`, `correctionResetThen_events`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/SourceInPlace.lean` — Annotated in-place arithmetic agrees with actual execution — `secp256k1MeasuredEEAForwardInDataBankSource`, `secp256k1InPlaceMultiplicationSource_certificate`, `secp256k1ZeroAllowedDivisionSource_certificate`, `secp256k1ZeroAllowedMultiplicationSource_certificate`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/SourcePoint.lean` — Annotated complete point circuit and selected correction-event bound — `pointConstantSourceEvents`, `fig14CoordinateSource_certificate`, `totalPointSource_certificate`, `pointAddSource_certificate`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/Square.lean` — Adaptive square-to-zero and modular square-add loop — `squareAdd`, `squareLoop_branch_correct`, `squareWrap_counts`, `secp256k1Square_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/SquareCoherent.lean` — Coherent square-loop forward/inverse correctness — `SquareInputValid`, `squareLoop_coherent`, `squareLoopInverse_coherent`, `squareLoop_forward_inverse_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/SquareInverse.lean` — Inverse square loop — `squareSub`, `secp256k1SquareInverse_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/SquareSubtract.lean` — Controlled square/subtract with clean work — `squareSubtract`, `squareSubtract_correct`, `squareSubtract_coherent`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/UncontrolledAdd.lean` — Uncontrolled Gidney constant-adder specialization — `gidneyAddConst`, `gidneyAddConst_branch_correct`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/UncontrolledCompare.lean` — Uncontrolled greater-or-equal comparator specialization — `gidneyCompareVirtualControl`, `gidneyCompareGE_branch_correct`, `secp256k1UncontrolledGidneyCompare_correct_resources`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/ZeroAllowed.lean` — Totalize in-place arithmetic at zero using prepare/restore — `nonzeroInputPrepare`, `nonzeroInputPrepare_run`, `nonzeroInputPrepareState_correct`, `fig15ZeroPrepare_run`.
- `ShorECDLP/Submission/2607_13816/Arithmetic/ZeroAllowedCoherent.lean` — Coherent zero-allowed division/multiplication — `secp256k1ZeroAllowedDivision_coherent`, `secp256k1ZeroAllowedMultiplication_coherent`.

## 2607_13816: EEA production interfaces

- `ShorECDLP/Submission/2607_13816/EEA/AdaptiveWrapper.lean` — Coherent EEA wrapper with explicit input-domain conditions — `Secp256k1EEAInputValid`, `eeaPreprocess_unpreprocess_coherent`, `secp256k1EEAReverseWrapper_coherent`, `secp256k1EEAForwardReverse_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/Bounds.lean` — Uniform termination/potential bounds and fixed-horizon padding certificate — `eeaGrowthBase`, `secp256k1_terminalPadding_certificate`.
- `ShorECDLP/Submission/2607_13816/EEA/IndexedStep.lean` — Actual indexed physical EEA step and arithmetic composition — `IndexedStepRegisters`, `indexedStepShiftPrefix_quotient_counter`, `indexedStepInverseAdaptive_coherent`, `indexedStepInverseAdaptive_tCount`.
- `ShorECDLP/Submission/2607_13816/EEA/InitialEncoding.lean` — Numeric input encoding and readiness of physical metadata — `lengthInitialize_size_correct`.
- `ShorECDLP/Submission/2607_13816/EEA/InitialPacked.lean` — Initial full packed-bank and metadata invariant — `eeaPreprocess_initial_workBanks`, `eeaPreprocess_initial_metadata`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredAnd.lean` — Measurement-assisted conjunction cleanup — `PathAndComputed`, `computeZeroAnd_tCount`, `eraseZeroAnd_coherent`, `eraseZeroAnd_tCount`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredLengthUpdates.lean` — Measured length updates with shared scratch — `measuredLenUpdateLtUnary`, `measuredLenUpdateLtUnary_coherent`, `measuredLenUpdateLrpUnary_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredPhysicalSupport.lean` — Physical support for the measured wrappers — `secp256k1MeasuredEEAReverseWrapper_wires_subset`, `secp256k1MeasuredEEAForwardWrapper_qubitCount`, `secp256k1MeasuredEEAReverseWrapper_qubitCount`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredPrimitiveCounts.lean` — Primitive gate vector for measured EEA blocks — `secp256k1MeasuredEEAReverseWrapper_primitive_exact`, `secp256k1MeasuredEEAForwardWrapper_primitive_bounds`, `secp256k1MeasuredEEAReverseWrapper_primitive_bounds`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredSchedule.lean` — Production measured forward/reverse EEA schedules — `measuredIndexedSchedule`, `measuredIndexedSchedule_coherent`, `measuredIndexedScheduleInverse_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredScheduleCounts.lean` — Counts for actual measured EEA production schedules — `secp256k1MeasuredEEAForward`, `secp256k1MeasuredEEAForward_coherent`, `secp256k1MeasuredEEAReverse_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredStep.lean` — Measurement-optimized complete EEA step — `measuredStepPrefix`, `measuredStepPrefix_coherent`, `measuredIndexedStep_coherent`, `measuredIndexedStepInverse_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredWorkspace.lean` — Measured EEA wrappers placed in the shared data bank — `secp256k1MeasuredEEAForwardInDataBank`, `secp256k1MeasuredEEAForwardInDataBank_coherent`, `secp256k1MeasuredEEAReverseWrapper_coherent_localImage`, `secp256k1MeasuredEEAReverseInDataBank_coherent_localImage`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredWrapper.lean` — Measured inversion wrappers on original input domains — `secp256k1MeasuredEEAForwardWrapper`, `secp256k1MeasuredEEAForwardWrapper_coherent`, `secp256k1MeasuredEEAReverseWrapper_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredWrapperCounts.lean` — Measured wrapper aggregate counts — `secp256k1MeasuredEEAReverseWrapper_savings`, `secp256k1MeasuredEEAForwardWrapper_toffoli`, `secp256k1MeasuredEEAReverseWrapper_toffoli`.
- `ShorECDLP/Submission/2607_13816/EEA/MeasuredZeroMap.lean` — Measured length-decoder/zero-map primitives — `measuredZeroPrefix`, `measuredRangeScan_coherent`, `measuredUpperZeroMap_coherent`, `measuredLowerZeroMap_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/Model.lean` — Pure four-phase extended-Euclidean microstep and invariants — `EEAState`, `paperStep`, `paperStep_preservesInvariant`, `paperRun_inverse_mod_prime`.
- `ShorECDLP/Submission/2607_13816/EEA/Preprocess.lean` — EEA input centering/preparation into physical work banks — `eeaLengthSetup`, `eeaPreprocess_branch_correct`, `eeaPreprocessIdealState_correct`, `eeaUnpreprocess_branch_correct`.
- `ShorECDLP/Submission/2607_13816/EEA/ProductionRun.lean` — Composition of physical EEA production execution — `secp256k1EEA_active_paperRun`, `secp256k1EEA_iteration_adaptiveInput`, `secp256k1EEA_active_adaptiveInput`.
- `ShorECDLP/Submission/2607_13816/EEA/Schedule.lean` — Forward/reverse fixed-horizon EEA schedule — `indexedStepRoutedState`, `secp256k1EEAForwardAdaptive_coherent`, `indexedScheduleInverseAdaptive_coherent`, `secp256k1EEAReverseAdaptive_coherent`.
- `ShorECDLP/Submission/2607_13816/EEA/ScheduleResources.lean` — Compositional resources for the complete EEA schedule — `secp256k1StepMeasurements`, `coefficientPrefix_leaf_count`, `secp256k1EEAForwardAdaptive_tCount`, `secp256k1EEAReverseAdaptive_tCount`.
- `ShorECDLP/Submission/2607_13816/EEA/SourceSchedules.lean` — Correction annotations for EEA schedules and erasure proofs — `secp256k1EEAForwardSource`, `secp256k1EEAForwardSource_certificate`, `secp256k1EEAReverseSource_certificate`.
- `ShorECDLP/Submission/2607_13816/EEA/Windows.lean` — Exact reference and certified active-window schedules — `activeWindows`, `certifiedActiveWindows`, `secp256k1_activeWindowCertificate_of_le`.
- `ShorECDLP/Submission/2607_13816/EEA/WorkspaceReuse.lean` — Relocate EEA banks into recycled point-arithmetic data registers — `eeaWorkspaceExchange`, `secp256k1EEAForwardInDataBank_coherent`, `secp256k1EEAReverseInDataBank_coherent`, `secp256k1EEAInDataBank_resources`.

## 2607_13816: Fourier and sample recovery

- `ShorECDLP/Submission/2607_13816/Fourier/Commutation.lean` — Disjoint Fourier/arithmetic branch commutation — `fourierBranch_mapDomain_commute`.
- `ShorECDLP/Submission/2607_13816/Fourier/Continuation.lean` — Fourier continuation after an existing measurement prefix — `fourierContinue`, `fourierContinue_run`, `fourierContinue_support`.
- `ShorECDLP/Submission/2607_13816/Fourier/FeedForward.lean` — Recorded phase corrections and semiclassical rotation feed-forward — `fourierControlledPhase`, `fourierFeedForward_projectZ_ket`, `fourierFeedForward_projectZ`, `fourierHistoryRotations_ket`.
- `ShorECDLP/Submission/2607_13816/Fourier/Kernel.lean` — Exact measured Fourier kernel with retained branch histories — `dyadicFourierKernel`, `semiclassicalFourier_run_kernel`.
- `ShorECDLP/Submission/2607_13816/Fourier/Relabel.lean` — Wire-permutation transport of measured Fourier execution — `fourierHistoryRotations_relabel`, `semiclassicalFourier_relabel`, `fourierContinue_relabel`.
- `ShorECDLP/Submission/2607_13816/Fourier/Semiclassical.lean` — Measured Fourier schedule with retained histories and explicit Kraus maps — `semiclassicalFourier`, `fourierBranch`, `semiclassicalFourier_run`, `semiclassicalFourier_measurements`.
- `ShorECDLP/Submission/2607_13816/Fourier/Support.lean` — Preservation of a valid-state support predicate under measured Fourier branches — `fourierBranch_supported`.

## 2607_13816: order finding

- `ShorECDLP/Submission/2607_13816/OrderFinding/AsymmetricPair.lean` — Asymmetric 256/208-bit two-sample distribution — `asymmetricPairMass`, `asymmetricPairPeak_injective`, `asymmetricPairPeak_mass`, `asymmetricPairMass_total`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/CyclicStates.lean` — Cyclic group-character states and orthogonality — `cyclicState`, `cyclicState_mass`, `cyclicShift_injective`, `cyclicState_shift`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/Normalization.lean` — Normalization of paired phase sampling — `decodePhysicalPairOutcome`, `physicalPairOutputMass_total`, `pointPhasePairProgram_normalized`, `physicalPairSuccessMass_le_one`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/PairSampling.lean` — Two-dimensional physical phase-sampling probabilities — `paperCharacterProduct`, `paperPairPeak_postprocess`, `paperPairPeak_mass`, `paperSuccessMass_lower`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/PeakMass.lean` — Character peak probability lower bounds — `paperPhaseAmplitude`, `nearNumerator_abs`, `paperPhasePeak_mass`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/PhaseProduct.lean` — Product form of repeated phase-sampling amplitudes — `phaseProduct`, `phaseProduct_eq_amplitude`, `phaseProduct_cons_point`, `phaseProduct_peak_mass`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/PhaseSchedule.lean` — Repeated recycled-control phase-sampling schedule — `pointPhaseSchedule`, `pointPhaseRecords_run`, `consumeAdaptiveHistory_run`, `pointPhaseSlice_run`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/PhaseStep.lean` — One recycled-control sampling step — `pointPhaseStepCoeff`, `pointPhaseStep_run`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/PhysicalPair.lean` — Physical paired-sampling distribution and success mass — `pointPhasePairProgram`, `pointPhasePairSlice_run`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/PointEigenstates.lean` — Physical point-translation eigenstates — `pointCyclicBasis`, `pointCyclicState_supported`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/Postprocess.lean` — Classical scalar recovery from paired samples — `NearNumerator`, `paperPostprocess_correct`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/ReducedCandidates.lean` — Finite candidate enumeration for reduced precision — `numeratorCandidates`, `numeratorCandidates_card`, `secp_numeratorCandidates_card`, `nearNumerator_shift_mem`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/ReducedCoverage.lean` — Candidate coverage for reduced-precision sample peaks — `reducedCoverageMass`, `asymmetricPairMass_nonneg`, `reducedCoverageMass_lower`, `reducedLeftPrecision_order`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/ReducedPeak.lean` — Reduced-precision peak estimates — `reducedPeakRaw`, `reducedPeakRaw_near`, `reducedPeakRaw_le`, `reducedPeak_mass`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/ReducedVerified.lean` — Accepted candidate correctness for reduced sampling — `reducedVerifiedCandidate`, `reducedVerifiedCandidate_complete`, `reducedVerifiedMass_eq`, `reducedVerifiedMass_lower`.
- `ShorECDLP/Submission/2607_13816/OrderFinding/WrappedCandidates.lean` — Wrapped-shift candidate list and mathematical coverage — `wrappedNumeratorCandidates`, `reducedShiftCandidates_correct`.

## 2607_13816: streaming execution and success

- `ShorECDLP/Submission/2607_13816/Window/DirectPointLookup.lean` — Direct initialization from the first point-table lookup — `pointTableMask`, `directPointLookup_tCount`, `physicalPointLookup_coherent`, `physicalPointLookup_resources`.
- `ShorECDLP/Submission/2607_13816/Window/OddTables.lean` — Odd-multiple point tables and their scalar interpretation — `oddWindowPoint`, `preparedOddWindowCall_correct`, `preparedOddWindowCallIndexed_correct`, `preparedOddWindowCallAt_correct`.
- `ShorECDLP/Submission/2607_13816/Window/PreparedArithmetic.lean` — Actual raw arithmetic on the original good-input component — `streamPreparedRawProgram`, `streamPreparedRaw_correct`, `streamPreparedRaw_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/PreparedEntry.lean` — Prepared arithmetic entry-state interface — `streamPreparedEntry`, `streamPreparedEntry_supported`, `streamPreparedGoodEntry_supported`.
- `ShorECDLP/Submission/2607_13816/Window/PreparedLookup.lean` — Initial lookup bridge with the complete non-point frame — `streamPreparedInitialState`, `streamBankLookup_coherent`, `streamPreparedLookup_coherent`, `streamPreparedArithmetic_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/PreparedSchedule.lean` — Physical prepared window calls and their schedule — `preparedWindowDelta`, `preparedWindowSchedule_coherent`, `preparedWindowScheduleState_correct`, `preparedWindowSchedule_support`.
- `ShorECDLP/Submission/2607_13816/Window/PreparedWeight.lean` — Good/bad prepared-input component mass — `streamPreparedWire`, `indexedStreamCalls_preparation`, `streamRawPreparation_eq`, `streamRawPrepared_excluded_mass`.
- `ShorECDLP/Submission/2607_13816/Window/RawAxisReuse.lean` — Relocate a full raw scalar axis into the streaming bank — `indexedStreamCalls`, `indexedStreamAxis_run`.
- `ShorECDLP/Submission/2607_13816/Window/RawBankReuse.lean` — Raw-call wire relocation into a single reused bank — `measuredRawBankBlock`, `measuredRawBankBlock_run`.
- `ShorECDLP/Submission/2607_13816/Window/RawCoordinate.lean` — Generic raw coordinate arithmetic in the window layout — `signedRawBeforeDivision`, `signedRawProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/RawDeferred.lean` — Raw streaming deferred-Fourier composition — `streamRawDeferredBody`, `streamRawPreparedBody_deferred`, `streamRawTrial_deferred`.
- `ShorECDLP/Submission/2607_13816/Window/RawFibers.lean` — Counting bad raw-coordinate inputs by fibers — `rawFirstWordState`, `rawAlgebraicExclusions_firstWord`, `reducedRawExclusions_firstWord_card`, `reducedRawExclusions_firstWord_fraction`.
- `ShorECDLP/Submission/2607_13816/Window/RawInitialize.lean` — First raw point lookup and entry state — `rawInitialState`, `initializedRawProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/RawInterference.lean` — Good/bad-subspace interference comparison — `reducedRawGoodEventMass`, `reducedRawEntryState_supported`.
- `ShorECDLP/Submission/2607_13816/Window/RawKernel.lean` — Raw scalar arithmetic and Fourier-kernel interface — `streamRawKernelBody`, `streamRawTrial_kernel`, `streamFourierWires_length`, `streamRawKernel_precisions`.
- `ShorECDLP/Submission/2607_13816/Window/RawPoint.lean` — Five-query raw signed coordinate program — `preparedRawPointInput`, `rawPointPath_correct`, `initializedRawPointPath_correct`, `initializedRawPointPath_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/RawRepetition.lean` — Physical raw reset/retry algorithm and success — `rawRepeatedProgram`, `rawRepeatedCandidate_mass`, `rawRepeatedCandidate_success`, `rawRepeatedProgram_zero`.
- `ShorECDLP/Submission/2607_13816/Window/RawSchedule.lean` — Prepared raw window-call sequence — `parkedRawProgram`, `parkedRawProgram_coherent`, `preparedRawProgram_coherent`, `rawWindowSchedule_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/RawStream.lean` — Actual streaming raw program with a recycled address bank — `streamRawCall`, `streamRawCall_support`, `streamRawTrial_support`, `streamRawCall_bank_run`.
- `ShorECDLP/Submission/2607_13816/Window/RawSuccess.lean` — Legacy raw trial acceptance/resource theorem — `reducedRawDecoder_success`, `reducedRawDecoder_independent_retry`.
- `ShorECDLP/Submission/2607_13816/Window/RawTwoAxis.lean` — Actual two-axis raw/streaming execution correspondence — `streamRawPreparedBody`, `streamRawTrial_prepared`.
- `ShorECDLP/Submission/2607_13816/Window/Recoding.lean` — Signed-window scalar recoding identities — `windowDigits`, `signedWindow_secp257_count`.
- `ShorECDLP/Submission/2607_13816/Window/ReducedContract.lean` — Legacy reduced-precision 256/208-bit contract — `ReducedSecpWindowContract`, `reducedSecpWindowContract`.
- `ShorECDLP/Submission/2607_13816/Window/ReducedNumericBounds.lean` — Closed numeric bounds for the reduced legacy implementation — `reducedWindowTrial_tCount_bound`, `reducedSecpWindow_tCount_bound`, `reducedSecpWindowRepeated_tCount_bound`.
- `ShorECDLP/Submission/2607_13816/Window/SignedAddress.lean` — Physical signed-address reflection and odd-table index — `signedTableAddress`, `signedAddressCircuit_run`, `signedAddressCircuit_tCount`.
- `ShorECDLP/Submission/2607_13816/Window/SignedCoordinate.lean` — Five-query signed affine coordinate composition — `signedLookupCoordinateProgram`, `signedLookupCoordinateProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/SignedLookup.lean` — Signed lookup-loaded modular addition — `signedLookupModularAddProgram`, `signedLookupModularAddProgram_coherent`, `signedLookupModularAddState_correct`, `signedLookupModularAddProgram_resources`.
- `ShorECDLP/Submission/2607_13816/Window/SignedPoint.lean` — Signed point addition including exceptional correction — `signedCorrectionX`, `correction_signed_address`, `signedLookupPointProgram_coherent`, `signedLookupPointState_correct`.
- `ShorECDLP/Submission/2607_13816/Window/StreamAllocation.lean` — Streaming address bank, physical allocation and resource count — `streamAddress`, `streamPointCall_support`, `streamPointLookup_support`, `streamScalarTrial_support`.
- `ShorECDLP/Submission/2607_13816/Window/StreamAssignedKernel.lean` — Point-state amplitudes for assigned streaming Fourier outputs — `streamFourierKernel_ket`, `streamFourierKernel_assigned`.
- `ShorECDLP/Submission/2607_13816/Window/StreamBlockClean.lean` — Clean reused address bank after measured blocks — `measuredStreamBlock`, `measuredStreamBlock_relabel_run`.
- `ShorECDLP/Submission/2607_13816/Window/StreamFibers.lean` — Bound excluded raw input fibers by 7/4096 — `streamRawX`, `streamRawInitialPoint_firstWord`, `streamRawExclusions_firstWord_card`, `streamRawExclusions_firstWord_fraction`.
- `ShorECDLP/Submission/2607_13816/Window/StreamGateCounts.lean` — Actual streaming primitive counts and abstract T bounds — `streamRepeatedProgram_gate_counts`, `streamRepeatedProgram_tCount_le`, `streamRepeatedProgram_gate_certificate`.
- `ShorECDLP/Submission/2607_13816/Window/StreamGoodFourier.lean` — Good-input component through final Fourier cleanup — `streamSelectedFourier`, `streamFourierKernelEventMass_root`, `streamRawFourierEventMass_terminal`, `streamPreparedGoodEntry_fourierMass`.
- `ShorECDLP/Submission/2607_13816/Window/StreamHistory.lean` — Full ordered arithmetic/Fourier histories through bank reuse — `streamBlockOutcomes`, `streamAxis_cons_run`, `streamAxis_cons_block_run`, `streamAxis_cons_reuse_run`.
- `ShorECDLP/Submission/2607_13816/Window/StreamHoist.lean` — Hoist clean-bank preparation across streaming arithmetic — `parkedStreamBody`, `streamBody_support`.
- `ShorECDLP/Submission/2607_13816/Window/StreamInterference.lean` — Actual acceptance comparison with the ideal selected event — `streamRawFourierEventMass_good_lower`, `streamPreparedScalarOutput_normSq`, `streamRawFourierEventMass_ideal_lower`.
- `ShorECDLP/Submission/2607_13816/Window/StreamKernel.lean` — Defer Fourier through disjoint future arithmetic — `streamFourierWires`, `streamFourierWires_nodup`, `deferredStreamAxis_measuredKernel`, `streamArithmeticPath_fourier_commute`.
- `ShorECDLP/Submission/2607_13816/Window/StreamPathMass.lean` — Sum all arithmetic branches for a fixed selected Fourier terminal — `streamArithmeticBulk`, `streamArithmeticPaths_sum`, `streamTwoArithmeticPaths_sum`, `streamRawFourierEventMass_bulk`.
- `ShorECDLP/Submission/2607_13816/Window/StreamPreparation.lean` — Prepare future banks without disturbing existing arithmetic — `streamRelabel_bank_disjoint`, `streamBlock_prepare_future`, `relocatedStreamAxis_future_commute`.
- `ShorECDLP/Submission/2607_13816/Window/StreamRecords.lean` — Parse chronological records into actual public Fourier samples — `consumeStreamFourier`, `streamRawPublicDecode_correct`.
- `ShorECDLP/Submission/2607_13816/Window/StreamResetRepetition.lean` — Branchwise zero reset and 56-trial ≥99% success — `streamResetWires`, `streamResetTrial_zero_support`, `streamRepeatedProgram_certificate`.
- `ShorECDLP/Submission/2607_13816/Window/StreamSamplingSuccess.lean` — Actual streaming ≥8% public-decoder acceptance and normalization — `streamRawTrial_success_certificate`.
- `ShorECDLP/Submission/2607_13816/Window/StreamScalar.lean` — Streaming arithmetic computes the two scalar sums coherently — `streamScalarValue`, `streamPreparedArithmetic_scalars_coherent`.
- `ShorECDLP/Submission/2607_13816/Window/StreamScalarWord.lean` — Match scalar inputs to physical Fourier-wire order — `streamScalarWires`, `streamPreparedScalar_fourierWords`, `streamPreparedScalar_fourierClear`, `streamPreparedFourierWires_clear`.
- `ShorECDLP/Submission/2607_13816/Window/StreamTightSupport.lean` — Remove unused wire 837: 854-wire/47471340504-record contract — `streamTightAllocation`, `preparedRawProgram_tight_support`, `streamRawTrial_tight_support`, `streamRepeatedProgram_tight_certificate`.
- `ShorECDLP/Submission/2607_13816/Window/StreamUniform.lean` — Uniform prepared phase-register expansion — `streamPreparedEntry_uniform`.
- `ShorECDLP/Submission/2607_13816/Window/StreamWeight.lean` — Translate raw exclusion counting into preparation Born mass — `streamLogicalPhaseWires`, `streamRawExclusions_word_count`.
- `ShorECDLP/Submission/2607_13816/Window/TableLookup.lean` — Measured unary QROM table lookup and coherent load/clear — `tableXorGates`, `tableLookupProgram_coherent`, `tableLookupProgram_coherent_clear`, `tableLookupProgram_16_256_resources`.
- `ShorECDLP/Submission/2607_13816/Window/TwoAxisHoist.lean` — Hoist preparation for both scalar axes — `unpreparedStreamAxis_future_commute`, `relocatedTwoAxis_hoist`.
- `ShorECDLP/Submission/2607_13816/Window/TwoAxisReuse.lean` — Connect both reused axes with their complete branch histories — `streamAxis_tail_run`.
- `ShorECDLP/Submission/2607_13816/Window/WeightedBlock.lean` — Weighted-call measured block and physical relocation equality — `measuredWeightedBlock_run`.

## 2607_13816: protected challenge migration (unfinished)

- `ShorECDLP/Submission/2607_13816/Challenge/AccumulatorEncoding.lean` — Bridge placed correction ports to the canonical 513-bit point encoding — `placedBatchState_pointWrite`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchCoherent.lean` — Coherent adaptive query/transposition implementation of the batch unitary — `batchSource_coherent`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchCost.lean` — Exact T cost of the five-word exceptional correction — `placedBatchSource_tCount`, `batchSchedule_cost`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchExecution.lean` — Batch readiness, valid schedule, matching result and scratch restoration — `BatchReady`, `batchUnitary_schedule`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchFrame.lean` — Complete non-data frame preservation by the batch unitary — `batchUnitary_fullFrame`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchPhysical.lean` — Physical well-formedness of batch queries and source program — `batchSource_wellFormed`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchPlacement.lean` — Place correction words/scratch at physical accumulator ports — `placedBatchProgram_run`, `placedBatchProgram_count`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchQuery.lean` — Physical query action matches XOR-word register model — `batchQuery_model`, `batchQuery_frame`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchState.lean` — Five-word register-level batch model and matching/cleanup — `batchModel_data`, `batchModel_clean`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchTemplate.lean` — Well-formedness of the protected batch template including inactive slots — `placedBatchProgram_wellFormed`.
- `ShorECDLP/Submission/2607_13816/Challenge/BatchedEndpoint.lean` — Four resident source words, one reused target and 14-query fixed correction — `batchSchedule`, `batchedEndpointProgram_run`, `batchedEndpointProgram_count`.
- `ShorECDLP/Submission/2607_13816/Challenge/CertificateAssembly.lean` — Candidate budget and conditional producer-to-protected-certificate interface — `StreamingAssembly`, `StreamingAssembly.certificate`, `streaming_candidate_budget`.
- `ShorECDLP/Submission/2607_13816/Challenge/Coefficient.lean` — Compile EEA coefficient-prefix arithmetic with execution and T agreement — `coefficientFirstProgram`, `coefficientProgram_tCount`, `coefficientInverseProgram_run`, `coefficientInverseProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Coefficients.lean` — Fixed point-table coefficient algebra and scalar interpretation — `coefficients`, `signedDigit_as_nsmul`, `firstWindowTable_coefficients`, `firstWindowCoefficients_point`.
- `ShorECDLP/Submission/2607_13816/Challenge/ConstantStraight.lean` — Compile constant-controlled gates into protected straight syntax — `constantTemplateGate`, `constantStraight_tCount`, `constantStraight_correction`, `constantStraight_deferred_run`.
- `ShorECDLP/Submission/2607_13816/Challenge/Coordinate.lean` — Compile zero-allowed division/multiplication and coordinate program — `zeroDivisionProgram`, `pointSquareProgram_tCount`, `coordinateProgram_run`, `coordinateProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/CoordinateConjugacy.lean` — Y-negation conjugacy of the repaired coordinate permutation — `fig14EncodedEquiv_negY`, `signedCorrection_negY`.
- `ShorECDLP/Submission/2607_13816/Challenge/CursorShift.lean` — Shift all transcript references and package fixed-count outer windows — `shiftStraight`, `closedWindow`, `closedWindow_run`.
- `ShorECDLP/Submission/2607_13816/Challenge/Dual.lean` — Compile dual-unary routing/erasure into fixed straight programs — `dualEraseProgram`, `dualEraseProgram_tCount`, `dualProgram_run`, `dualProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/EEACenter.lean` — Compile EEA centering, parity and constant-minus preparation — `constMinusProgram`, `eeaUncenterProgram_tCount`, `eeaParityProgram_run`, `eeaParityProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Endpoint.lean` — Compile endpoint writers and EEA end-iteration blocks — `upperEndProgram`, `hProgram_tCount`, `hInverseProgram_run`, `hInverseProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/EndpointCoherent.lean` — Coherent adaptive exceptional-endpoint query sandwich — `endpointQueryAdaptive`, `endpointQueryMatching_coherent`, `endpointQueryMatchingProgram_run`, `endpointQueryMatchingProgram_coherent`.
- `ShorECDLP/Submission/2607_13816/Challenge/EndpointEncoding.lean` — Bind protected exceptional fields to encoded endpoint words — `coordinateWordBits`, `readEndpointWords_correct`, `bitLoad_matching_correct`.
- `ShorECDLP/Submission/2607_13816/Challenge/EndpointLoad.lean` — Fixed exceptional-endpoint bit loads from protected fields — `EndpointBit`, `bitLoadCircuit_value`, `bitLoadCircuit_involutive`, `exceptionalEndpointPorts_length`.
- `ShorECDLP/Submission/2607_13816/Challenge/EndpointQROM.lean` — Unary QROM selection of exceptional endpoint words — `endpointTagMask`, `endpointXorPair_run`, `endpointLookup_coherent`, `endpointLookup_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/EndpointSandwich.lean` — Query/transposition sandwich action with endpoint restoration — `endpointQuery`, `normalizedEndpointWords_correct`.
- `ShorECDLP/Submission/2607_13816/Challenge/EndpointSwap.lean` — Runtime-word endpoint transposition circuit and T cost — `endpointFlag`, `endpointBitCircuit_run`, `endpointWordCircuit_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/EndpointTransposition.lean` — Compile physical equality-controlled endpoint transpositions — `equalityCells`, `endpointTransposition_coherent`, `endpointTranspositionProgram_run`, `endpointTranspositionProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/ExceptionalFields.lean` — Protected exceptional fields agree with mathematical exception pairs — `exceptionFieldCoordinates`, `protectedExceptionPairs_correct`.
- `ShorECDLP/Submission/2607_13816/Challenge/FixedMatching.lean` — Fixed finite matching schedule repairing exceptional inputs — `fixedExceptionInputs`, `fixedMatching_correct`, `fixedExceptionSwaps_correct`.
- `ShorECDLP/Submission/2607_13816/Challenge/FixedNetwork.lean` — Fixed comparison/transposition network geometry — `MatchingSlot`, `matchingMoveCircuit_correct`, `matchingMovesCircuit_correct`, `matchingCircuit_correct`.
- `ShorECDLP/Submission/2607_13816/Challenge/Fourier.lean` — Compile semiclassical Fourier with absolute record feedback — `fourierProgram`, `fourierProgram_wellFormed`.
- `ShorECDLP/Submission/2607_13816/Challenge/Gates.lean` — Literal gate/record compiler and fixed-shape lookup leaves — `gateProgram`, `gateProgram_run`.
- `ShorECDLP/Submission/2607_13816/Challenge/GidneyAdd.lean` — Compile measured Gidney adder and all correction records — `gidneyCarryCells`, `gidneyNontrivialProgram_tCount`, `gidneyProgram_run`, `gidneyProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/GidneyCompare.lean` — Compile controlled/uncontrolled measured comparison — `compareCarryCells`, `compareGEProgram_constant_run`, `uncontrolledCompareProgram_run`, `uncontrolledCompareProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Horner.lean` — Compile adaptive Horner multiply/inverse into protected syntax — `modularSubProgram`, `hornerProgram_tCount`, `hornerInverseProgram_run`, `hornerInverseProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/InPlace.lean` — Compile measured in-place multiplication/division — `multiplyWorkProgram`, `multiplicationAfterResetProgram_tCount`, `multiplicationProgram_run`, `multiplicationProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/IndexedStep.lean` — Compile original indexed EEA forward/inverse step — `remainderBlockSources`, `indexedStepProgram_tCount`, `indexedInverseStepProgram_run`, `indexedInverseStepProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Interval.lean` — Compile interval traversal, equality and routing primitives — `equalityProgram`, `traversalFirstProgram_tCount`, `traversalSecondProgram_run`, `traversalSecondProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/IntervalWhole.lean` — Compile complete active-interval arithmetic and inverse — `intervalTopFirstProgram`, `intervalProgram_tCount`, `intervalInverseProgram_run`, `intervalInverseProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/LengthRefresh.lean` — Compile measured length-refresh writers and updates — `upperWriterProgram`, `ltUpdateProgram_tCount`, `lrpUpdateProgram_run`, `lrpUpdateProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Lookup.lean` — Compile measured unary QROM operations with T agreement — `literalProgram`, `recordGates_tCount`, `andEraseProgram_tCount`, `lookupProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/LookupPhysical.lean` — Well-formedness of lookup operations including optional slots — `LookupOp.Physical`, `lookupProgram_wellFormed`, `ordinaryOp_physical`, `unaryLookupOps_physical`.
- `ShorECDLP/Submission/2607_13816/Challenge/MatchingPhysical.lean` — Physical validity of equality and matching/transposition circuits — `equalityCells_wellFormed`, `endpointTransposition_wellFormed`, `matchingCircuit_wellFormed`.
- `ShorECDLP/Submission/2607_13816/Challenge/MeasuredSchedule.lean` — Compile production measured EEA forward/reverse schedules — `measuredScheduleProgram`, `measuredEEAForwardProgram_tCount`, `measuredEEAReverseProgram_run`, `measuredEEAReverseProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/MeasuredStep.lean` — Compile the complete measured EEA step and inverse — `measuredStepSources`, `measuredStepProgram_tCount`, `measuredInverseStepProgram_run`, `measuredInverseStepProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/MeasuredWorkspace.lean` — Compile measured EEA wrappers relocated into data banks — `measuredForwardDataBankProgram`, `measuredForwardDataBankProgram_tCount`, `measuredReverseDataBankProgram_run`, `measuredReverseDataBankProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/MeasuredWrapper.lean` — Compile measured inversion wrapper stages and cleanup — `measuredForwardWrapperSources`, `measuredForwardWrapperProgram_tCount`, `measuredReverseWrapperProgram_run`, `measuredReverseWrapperProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/ModularAdd.lean` — Compile measured modular word addition — `appendCompiled`, `literalProgram_tCount`, `appendCompiled_tCount`, `modularAddProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/ModularNegate.lean` — Compile signed modular negation and negative-control wrappers — `prependCompiled`, `modularNegateProgram_tCount`, `negativeNegateProgram_run`, `negativeNegateProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/OddFields.lean` — Fixed odd-window coefficient references and field consistency — `OddWindow`, `fieldLoadProgram_run`, `fieldLoadProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Outer.lean` — Actual parameterized 56-round outer program and Fourier record binding — `OuterWindow`, `OuterPlan`, `standardOuterPlan`, `OuterPlan.entry_reads`.
- `ShorECDLP/Submission/2607_13816/Challenge/OuterResources.lean` — Uniform per-window S/T/M and shared support imply whole-entry bounds — `OuterBudget`, `OuterBudget.resources`, `OuterBudget.assembly`.
- `ShorECDLP/Submission/2607_13816/Challenge/OuterTrace.lean` — Split actual sequential branches with their chronological histories — `straight_append_branch`.
- `ShorECDLP/Submission/2607_13816/Challenge/Phase.lean` — Compile EEA phase-update cores and their inverses — `phaseCoreGates`, `phaseProgram_tCount`, `phaseInverseProgram_run`, `phaseInverseProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/PlacedBatch.lean` — Physical/coherent placement of the correction's full state action — `placedBatchSource_state`.
- `ShorECDLP/Submission/2607_13816/Challenge/PointTable.lean` — Compile point-coordinate table access and direct first lookup — `pointRefs`, `firstLookupProgram_run`, `firstLookupProgram_tCount`, `firstWindowProgram_run`.
- `ShorECDLP/Submission/2607_13816/Challenge/Positions.lean` — Legacy 256/208-bit layout parameters and historical record positions — `legacyDecoderParams`, `legacyTrialStride`, `legacyDecodeLayout`.
- `ShorECDLP/Submission/2607_13816/Challenge/RangeScan.lean` — Compile location-controlled range scans — `rangeLeafProgram`, `rangeLeafProgram_tCount`, `rangeScanProgram_run`, `rangeScanProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Records.lean` — Exact branch-history lengths for Straight/reset programs — `straight_history_length`, `fixedReset_history_length`.
- `ShorECDLP/Submission/2607_13816/Challenge/RegisterCorrection.lean` — Compile measured register Z corrections with fixed record indices — `registerCorrectionProgram`, `literalProgram_append_tCount`, `deferredCorrectionCircuit_tCount`, `deferredCorrectionProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/RegisterEquality.lean` — Physical XOR-word equality circuits and straight compilation — `xorWordCircuit`, `registerEqualAdaptive_coherent`, `registerEqualProgram_run`, `registerEqualProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Reindex.lean` — Transport protected constant-bit/table references across shared tables — `reindexBit`, `reindexStraight_instantiate`, `reindexStraight_gateSlots`, `readConstant_reindex`.
- `ShorECDLP/Submission/2607_13816/Challenge/Relabel.lean` — Transport protected programs through physical wire permutations — `relabelTemplateGate`, `relabelCompiled_run`, `relabelCompiled_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Reset.lean` — Fixed legacy reset support and compiled reset program — `resetWires`, `resetWires_length`, `fixedReset_run`.
- `ShorECDLP/Submission/2607_13816/Challenge/RetainedRecords.lean` — Append compilers while preserving earlier measurement references — `HistoryAgrees`, `collectProgram_tCount`, `appendRetaining_run`, `appendRetaining_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Schedule.lean` — Compile original EEA schedules and forward/reverse execution — `scheduleProgram`, `eeaForwardProgram_tCount`, `eeaReverseProgram_run`, `eeaReverseProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Sequence.lean` — Compose fixed-count compiled stages and their instrument equalities — `FixedSegment`, `sequenceProgram`, `sequenceProgram_run`.
- `ShorECDLP/Submission/2607_13816/Challenge/SharedTable.lean` — Shared 983040-row table and first/odd-window field reference adapters — `coefficientAt`, `sharedCoordinateProgram_run`.
- `ShorECDLP/Submission/2607_13816/Challenge/SignedWindow.lean` — Compile signed point-field and Y-negation stages — `yNegateProgram`, `fieldLookupAddProgram_tCount_source`, `yNegateProgram_tCount`, `signedFieldProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Square.lean` — Compile square/inverse and controlled square-subtract — `squareAddProgram`, `squareInverseProgram_tCount`, `squareSubtractProgram_run`, `squareSubtractProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Support.lean` — Legacy tight support and fixed-reset-to-zero bridge — `rawTrial_support_resetWires`, `reset_supported_program_zero`.
- `ShorECDLP/Submission/2607_13816/Challenge/Unary.lean` — Compile unary routing and measurement-assisted erasure — `zeroEraseProgram`, `unaryProgram_run`, `zeroEraseProgram_tCount`, `unaryProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/VChain.lean` — Compile multi-control chain and interval ripple primitives — `vchainTailProgram`, `rippleFirstProgram_tCount`, `rippleSecondProgram_run`, `rippleSecondProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/WindowBody.lean` — Concrete first lookup, 28 correction-bearing windows and outer-plan assembly — `actualBatchedWindow`, `batchedOuterPlan`, `batchedResetWires_length`.
- `ShorECDLP/Submission/2607_13816/Challenge/WindowModular.lean` — Compile lookup-loaded modular additions in shared coordinate arithmetic — `fieldLookupAddProgram`, `fieldLookupAddProgram_run`, `fieldLookupAddProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/WindowNegation.lean` — Canonical signed modular-negation result with full external frame — `windowYNegate_coherent`, `windowYNegateState_pointWrite`.
- `ShorECDLP/Submission/2607_13816/Challenge/Workspace.lean` — Compile original EEA bank-reuse wrappers — `forwardDataBankProgram`, `forwardDataBankProgram_tCount`, `reverseDataBankProgram_run`, `reverseDataBankProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/Wrapper.lean` — Compose literal surrounds and inversion-wrapper compilation — `surroundCompiled`, `forwardWrapperProgram_tCount`, `reverseWrapperProgram_run`, `reverseWrapperProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/ZeroLeaf.lean` — Compile zero-decoder leaves with measured cleanup — `zeroCellProgram`, `lowerForwardLeafProgram_tCount`, `lowerReverseLeafProgram_run`, `lowerReverseLeafProgram_tCount`.
- `ShorECDLP/Submission/2607_13816/Challenge/ZeroMap.lean` — Compile upper/lower zero maps and their resources — `upperMapProgram`, `upperMapProgram_tCount`, `lowerMapProgram_run`, `lowerMapProgram_tCount`.

## Protected judge outside the requested directories

- `ShorECDLP/Judge/Main.lean` — Trusted admission predicate consumed by the benchmark — `acceptance`, `extendedAcceptance`.
