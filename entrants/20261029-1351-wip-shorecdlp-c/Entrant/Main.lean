import ShorECDLP.Submission.Entrant.WindowMass
import ShorECDLP.Challenge.Official
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Challenge.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStepPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
import ShorECDLP.Submission.«2607_13816».EEA.WrapperPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Window.PhysicalRepetition
import ShorECDLP.Submission.«2607_13816».Window.RawDistribution
import ShorECDLP.Submission.«2607_13816».Window.Repetition
import ShorECDLP.Submission.«2607_13816».Window.StreamSamplingSuccess
import ShorECDLP.Submission.«2607_13816».Window.Uniform

/-!
Construction and proofs from VerifiedQC/ShorECDLP,
lamport/challenge-final-certificate @ b46e337 (Apache-2.0).
Our contribution: a uniform per-round acceptance bound of 0.546,
using finite Fourier moments; the entry uses 6 rounds.
The entry and decoder share streamingRounds.
Packaged into existing tracked files for the official source policy;
workspace/port_upstream.py and workspace/package_streaming.py reproduce it.
-/

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.DecoderBridge -/
section Port_DecoderBridge

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
open scoped BigOperators

theorem fixedCandidates_legacy_eq (out : Fin (2^256) × Fin (2^208)) :
    fixedCandidates legacyDecoderParams out.1.val out.2.val = reducedShiftCandidates order 256 208 out := rfl

theorem wrappedPairAccept_legacy_iff (Q : Point) (out : Fin (2^256) × Fin (2^208)) :
    wrappedPairAccept legacyDecoderParams Q out.1.val out.2.val = true ↔
      (reducedVerifiedCandidate Q out).isSome = true := by
  classical
  rw [wrappedPairAccept,fixedCandidates_legacy_eq]
  simp only [List.find?_isSome,Finset.mem_toList,decide_eq_true_eq]
  unfold reducedVerifiedCandidate
  split_ifs with h
  · simp only [Option.isSome_some,iff_true]; exact h
  · simp only [Option.isSome_none,Bool.false_eq_true,iff_false]; exact h

attribute [local irreducible] wrappedPairAccept reducedVerifiedCandidate

theorem old_accept_implies_wrapped (Q : Point) (out : List Bool × List Bool)
    (h : reducedRawDecoderAccept Q out = true) :
    wrappedPairAccept legacyDecoderParams Q (fourierWordLSB out.1) (fourierWordLSB out.2) = true := by
  unfold reducedRawDecoderAccept reducedRawPublicDecode at h
  split_ifs at h with hl
  · let out' : Fin (2^256) × Fin (2^208) :=
      (⟨fourierWordLSB out.1, by simpa [hl.1] using fourierWordLSB_lt out.1⟩,
       ⟨fourierWordLSB out.2, by simpa [hl.2] using fourierWordLSB_lt out.2⟩)
    exact (wrappedPairAccept_legacy_iff Q out').mpr h
  · simp at h

theorem wrappedAccept_paperOutcomes (Q : Point) (out : Fin (2^256) × Fin (2^208)) :
    wrappedPairAccept legacyDecoderParams Q
      (fourierWordLSB (paperOutcomeBits 256 out.1)) (fourierWordLSB (paperOutcomeBits 208 out.2)) =
      reducedRawDecoderAccept Q (paperOutcomeBits 256 out.1,paperOutcomeBits 208 out.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [paperOutcomeBits_word]
  rw [wrappedPairAccept_legacy_iff]
  simp [reducedRawDecoderAccept,reducedRawPublicDecode,paperOutcomeBits_length,paperOutcomeBits_word]

theorem wrappedIdeal_mass_eq (Q : Point) (hG : G≠0) (hQ : Q≠0) (hrQ : order • Q=0) :
    reducedRawIdealFourierEventMass G Q
      (fun xy => wrappedPairAccept legacyDecoderParams Q (fourierWordLSB xy.1) (fourierWordLSB xy.2)) =
      reducedRawIdealFourierEventMass G Q (reducedRawDecoderAccept Q) := by
  rw [reducedRawIdealFourierEventMass_distribution G Q hG hQ generator_nsmul_eq_zero hrQ,
      reducedRawIdealFourierEventMass_distribution G Q hG hQ generator_nsmul_eq_zero hrQ]
  apply Finset.sum_congr rfl
  intro out _
  rw [wrappedAccept_paperOutcomes]

theorem wrappedIdeal_mass_lower (Q : Point) (hG : G≠0) (hQ : Q≠0) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    (546:ℝ)/1000 ≤ reducedRawIdealFourierEventMass G Q
      (fun xy => wrappedPairAccept legacyDecoderParams Q (fourierWordLSB xy.1) (fourierWordLSB xy.2)) := by
  rw [wrappedIdeal_mass_eq Q hG hQ hrQ,reducedRawIdealDecoder_eq Q hG hQ hrQ d hQd]
  rw [reducedPhysicalVerifiedMass_eq Q hG hQ hrQ d hQd]
  exact ShorECDLP.Acceptance.secpVerified_546 Q d hQ hQd
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_DecoderBridge

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.MeasurementBridge -/
section Port_MeasurementBridge

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The branch tree retains every measurement outcome, including zero-mass branches. -/
theorem adaptive_run_nonempty (a : AdaptiveCircuit) : ∃ b, b ∈ a.run := by
  induction a with
  | done => exact ⟨_, List.mem_singleton_self _⟩
  | unitary gs a ih =>
    obtain ⟨b,hb⟩ := ih
    exact ⟨_, List.mem_map_of_mem hb⟩
  | xMeasureReset w a b iha ihb =>
    obtain ⟨c,hc⟩ := iha
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hc)⟩

/-- Uniform actual branch record lengths determine the syntactic measurement count. -/
theorem measurementCount_of_uniform_run (a : AdaptiveCircuit) (k : Nat)
    (h : ∀ b ∈ a.run, b.history.length = k) : a.measurementCount = k := by
  induction a generalizing k with
  | done => exact h ⟨[],LinearMap.id⟩ (List.mem_singleton_self _)
  | unitary gs a ih =>
    apply ih
    intro b hb
    have hh := h _ (List.mem_map.mpr ⟨b,hb,rfl⟩)
    exact hh
  | xMeasureReset w a b iha ihb =>
    have ha : ∀ c ∈ a.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_left _ (List.mem_map_of_mem hc))
    have hb : ∀ c ∈ b.run, c.history.length + 1 = k := by
      intro c hc
      exact h _ (List.mem_append_right _ (List.mem_map_of_mem hc))
    have hk : 0 < k := by
      obtain ⟨c,hc⟩ := adaptive_run_nonempty a
      have := ha c hc
      omega
    have hca := iha (k-1) (by intro c hc; have := ha c hc; omega)
    have hcb := ihb (k-1) (by intro c hc; have := hb c hc; omega)
    simp only [AdaptiveCircuit.measurementCount,hca,hcb,max_self]
    omega

/-- Transfer measurement counts through a proved execution binding, without
unfolding the compiled circuit or enumerating its branches. -/
theorem compiled_count_of_run {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (a : AdaptiveCircuit)
    (h : compiledRun p read history = a.run) : p.1 = a.measurementCount := by
  apply Eq.symm
  apply measurementCount_of_uniform_run
  intro b hb
  rw [← h] at hb
  have hh := straight_history_length p.2 read history b hb
  simpa using hh
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_MeasurementBridge

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowCounts -/
section Port_WindowCounts

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] sharedCoordinateProgram yNegateProgram placedBatchProgram
  batchedWindowCore batchedWindowPrepared signedLookupCoordinateProgram primitiveResources
  sharedYNegateProgram actualBatchedWindow actualLeftWindows actualRightWindows
  placedBatchSource windowYNegate sequenceCircuit batchedWindowSources

private theorem port_WindowCounts_adder_counts : pointLookupAdderPrimitives.toffoli=2813 ∧
    pointLookupAdderPrimitives.phase=0 ∧ pointLookupAdderPrimitives.measurements=511 := by
  decide +kernel
private theorem port_WindowCounts_lookup_counts (table : Nat → Nat) :
    (pointLookupPrimitives table).toffoli=68347 ∧
    (pointLookupPrimitives table).phase=0 ∧ (pointLookupPrimitives table).measurements=66045 := by
  simp only [pointLookupPrimitives,lookupWordPrimitives,pointLookupAddress,List.length_range',
    PrimitiveResources.add,port_WindowCounts_adder_counts.1,port_WindowCounts_adder_counts.2.1,port_WindowCounts_adder_counts.2.2]
  decide

/-- Source coordinate arithmetic includes both zero-allowed field operations. -/
theorem coordinate_numeric_counts (x y : Nat → Nat) :
    (signedLookupCoordinateProgram x y).tCount = 510203526 ∧
    (signedLookupCoordinateProgram x y).measurementCount = 30272702 := by
  have h : (primitiveResources (signedLookupCoordinateProgram x y)).toffoli = 72886218 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).phase = 0 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).measurements = 30272702 := by
    rw [signedLookupCoordinateProgram_primitive]
    simp only [signedCoordinatePrimitives,signedPointLookupPrimitives,PrimitiveResources.add,
      (port_WindowCounts_lookup_counts _).1,(port_WindowCounts_lookup_counts _).2.1,(port_WindowCounts_lookup_counts _).2.2]
    decide
  have ht := primitiveResources_T_of_no_phase _ h.2.1
  rw [h.1] at ht
  exact ⟨ht,by simpa only [primitiveResources] using h.2.2⟩

/-- One actual sign-negation segment, including its two X wrappers. -/
theorem windowYNegate_numeric_counts :
    windowYNegate.tCount = 21434 ∧ windowYNegate.measurementCount = 1022 := by
  have h := controlledModularNegate256_primitive_exact (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558 (by simp) (by simp) (by simp)
  have he : primitiveResources (controlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558)=⟨3068,4088,12983,3062,0,1022⟩ := by
    rw [h]
    decide +kernel
  have ht := primitiveResources_T_of_no_phase _ (congrArg PrimitiveResources.phase he)
  rw [he] at ht
  have hm := congrArg PrimitiveResources.measurements he
  have hn := negativeControlledModularNegate_resources (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558
  unfold windowYNegate
  rw [hn.1,hn.2]
  constructor
  · exact ht
  · simpa only [primitiveResources] using hm

theorem sharedCoordinateProgram_count (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).1 = 30272702 := by
  have h := compiled_count_of_run (sharedCoordinateProgram w start)
    (readConstant coefficientAt (0 : Point)) (fun _ => false) _
    (sharedCoordinateProgram_run w start 0 (by simp) (fun _ => false))
  exact h.trans (coordinate_numeric_counts _ _).2

theorem sharedYNegateProgram_count (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).1 = 1022 := by
  exact (compiled_count_of_run _ (fun _ => false) (fun _ => false) _
    (sharedYNegateProgram_run w start (fun _ => false) (fun _ => false))).trans
    windowYNegate_numeric_counts.2

theorem placedBatchProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (placedBatchProgram w start) (readConstant coefficientAt Q) history =
      (placedBatchSource Q w).tCount := by
  simp only [placedBatchProgram,relabelCompiled,compiledTCount,relabelStraight_instantiate,
    AdaptiveCircuit.relabel_tCount,batchedEndpointProgram,lookupProgram_tCount,batchOps_source,
    placedBatchSource]

theorem sharedYNegateProgram_tCount (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedYNegateProgram w start) read history = windowYNegate.tCount := by
  simp only [sharedYNegateProgram,reindexCompiled,compiledTCount,reindexStraight_instantiate]
  unfold windowYNegate
  exact yNegateProgram_tCount start _ history

theorem batchedWindowCore_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    compiledTCount (batchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (batchedWindowSources Q w)).tCount := by
  unfold batchedWindowCore
  apply sequenceProgram_tCount
  unfold batchedWindowSegments batchedWindowSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact sharedCoordinateProgram_tCount w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h
  · intro cursor h; exact placedBatchProgram_tCount w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h

theorem sequenceCircuit_four_tCount (a b c d : AdaptiveCircuit) :
    (sequenceCircuit [a,b,c,d]).tCount = a.tCount+b.tCount+c.tCount+d.tCount := by
  simp only [sequenceCircuit,adaptive_tCount_seq,AdaptiveCircuit.tCount]
  omega

theorem batchedWindowSources_tCount (Q : Point) (w : OddWindow) :
    (sequenceCircuit (batchedWindowSources Q w)).tCount = 514030776 := by
  unfold batchedWindowSources
  rw [sequenceCircuit_four_tCount,(coordinate_numeric_counts _ _).1,
    windowYNegate_numeric_counts.1,placedBatchSource_tCount]

theorem actualFirstWindow_tCount (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 458745 := by
  simp only [actualFirstWindow,reindexStraight_instantiate,
    readConstant_reindex firstIndex _ _ Q coefficientAt_first]
  exact firstLookupProgram_tCount start Q hQ history

theorem actualBatchedWindow_tCount (w : OddWindow) (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount =
      514030776 := by
  have h := surroundCompiled_tCount (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (batchedWindowCore w 0)
    (sequenceCircuit (batchedWindowSources Q w)) (readConstant coefficientAt Q) Fin.elim0
    (batchedWindowCore_tCount w 0 Q hQ Fin.elim0)
  simp only [AdaptiveCircuit.tCount,adaptive_tCount_seq,signedAddressCircuit_tCount,
    Nat.zero_add,Nat.add_zero,batchedWindowSources_tCount] at h
  simp only [actualBatchedWindow,closedWindow_run,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  change compiledTCount (batchedWindowPrepared w 0) (readConstant coefficientAt Q) Fin.elim0 = _
  unfold batchedWindowPrepared
  exact h

theorem batchedWindowCore_count (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).1 = 30733484 := by
  simp only [batchedWindowCore,batchedWindowSegments,sequenceProgram,appendCompiled,
    sharedCoordinateProgram_count,sharedYNegateProgram_count,placedBatchProgram_count]

theorem surroundCompiled_count {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (surroundCompiled before after p).1 = p.1 := by
  simp only [surroundCompiled,prependCompiled,appendCompiled,Nat.add_zero]

theorem actualBatchedWindow_count (w : OddWindow) :
    (actualBatchedWindow w).count = 30733484 := by
  unfold actualBatchedWindow closedWindow
  change 0 + (batchedWindowPrepared w 0).1 = 30733484
  rw [Nat.zero_add]
  have hp : (batchedWindowPrepared w 0).1 = (batchedWindowCore w 0).1 := by
    unfold batchedWindowPrepared
    exact surroundCompiled_count _ _ _
  rw [hp,batchedWindowCore_count]

theorem actualFirstWindow_count : actualFirstWindow.count = 65535 := rfl

theorem axisCount_constant {n : Nat} (ws : List (OuterWindow n)) (m : Nat)
    (hm : ∀ w ∈ ws, w.count = m) : axisCount ws = ws.length * (m+16) := by
  induction ws with
  | nil => simp [axisCount]
  | cons w ws ih =>
    rw [axisCount,hm w (by simp),ih (by intro v hv; exact hm v (by simp [hv]))]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem actualLeftWindows_count : axisCount actualLeftWindows = 461068051 := by
  unfold actualLeftWindows
  rw [axisCount,actualFirstWindow_count]
  rw [axisCount_constant _ 30733484]
  · simp
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact actualBatchedWindow_count _

theorem actualRightWindows_count : axisCount actualRightWindows = 399535500 := by
  unfold actualRightWindows
  rw [axisCount_constant _ 30733484]
  · simp
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact actualBatchedWindow_count _

theorem standardOuterPlan_lists_stride {n : Nat} (left right : List (OuterWindow n))
    (hl : left.length = 16) (hr : right.length = 13) (reset : List Wire) :
    (standardOuterPlan ⟨left.toArray,by simpa using hl⟩
      ⟨right.toArray,by simpa using hr⟩ reset).stride =
      axisCount left + axisCount right + reset.length := by
  simp only [OuterPlan.stride,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem batchedOuterPlan_stride : batchedOuterPlan.stride = 860607482 := by
  have h := standardOuterPlan_lists_stride actualLeftWindows actualRightWindows
    actualLeftWindows_length actualRightWindows_length batchedResetWires
  apply h.trans
  rw [actualLeftWindows_count,actualRightWindows_count,batchedResetWires_length]

/-- Exact final record count includes the first lookup, all 28 addition windows,
all Fourier measurements, and the full 3931-wire reset in each of 6 rounds. -/
theorem batchedOuterPlan_finalCursor : streamingRounds * batchedOuterPlan.stride = 5163644892 := by
  rw [batchedOuterPlan_stride]
  norm_num [streamingRounds]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WindowCounts

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowBudget -/
section Port_WindowBudget

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] actualFirstWindow actualBatchedWindow actualLeftWindows actualRightWindows
  batchedOuterPlan

/-- Weighted window costs retain the much smaller first lookup. -/
theorem outerAxis_weighted_t_le {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (cost : OuterWindow n → Nat) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ ws, ∀ s h, ((w.program s).instantiate read h).tCount ≤ cost w)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((outerAxis wires ws start prior).instantiate read history).tCount ≤
      (ws.map cost).sum + axisFeedback ws.length prior.length := by
  induction ws generalizing start with
  | nil => simp [outerAxis,axisFeedback,Straight.instantiate,AdaptiveCircuit.tCount]
  | cons w ws ih =>
    simp only [outerAxis,castFinish_instantiate]
    apply (outer_append_t_le _ _ read history
      (fourierSlots 16 prior.length + ((ws.map cost).sum+axisFeedback ws.length (prior.length+16))) ?_).trans
    · simp only [prepareOuterBank_t,List.length_cons,List.map_cons,List.sum_cons,axisFeedback]
      have h := hw w (by simp) start history
      omega
    · intro h
      apply (outer_append_t_le _ _ read h
        ((ws.map cost).sum+axisFeedback ws.length (prior.length+16)) ?_).trans
      · have hf := fourierProgram_t_le n .inverse wires.toList (start+w.count) (bankPrior w.count prior) read h
        simp only [Vector.length_toList,bankPrior_length] at hf
        simp only [castFinish_instantiate]
        omega
      · intro h₂
        simpa only [nextBankPrior_length] using
          ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ (nextBankPrior w.count prior) h₂

theorem OuterPlan.round_weighted_t_le {n : Nat} (p : OuterPlan n)
    (cost : OuterWindow n → Nat) (read : ConstantBit n → Bool)
    (hw : ∀ w ∈ p.left.toList ++ p.right.toList, ∀ s h,
      ((w.program s).instantiate read h).tCount ≤ cost w)
    (start : Nat) (history : Fin start → Bool) :
    ((p.round start).instantiate read history).tCount ≤
      (p.left.toList.map cost).sum + (p.right.toList.map cost).sum + 54168 := by
  have hl := outerAxis_weighted_t_le p.wires p.left.toList cost read
    (fun w h => hw w (List.mem_append_left _ h)) start List.nil history
  have hr (h) := outerAxis_weighted_t_le p.wires p.right.toList cost read
    (fun w h => hw w (List.mem_append_right _ h)) (start+axisCount p.left.toList) List.nil h
  simp only [Vector.length_toList,List.length_nil] at hl hr
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,TemplateGate.instantiate,
    AdaptiveCircuit.tCount,ShorECDLP.tCount,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    tCost,Nat.zero_add]
  apply (outer_append_t_le _ _ read history ((p.right.toList.map cost).sum+axisFeedback 13 0) ?_).trans
  · have h := outer_feedback_overhead; omega
  · intro h
    apply (outer_append_t_le _ _ read h 0 ?_).trans
    · have ht := hr h; omega
    · intro h₂
      simp [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.tCount,
        ShorECDLP.tCount,tCost,resetProgram_t]

def actualWindowTCost (w : OuterWindow 983040) : Nat :=
  if w.count = 65535 then 458745 else 514030776

theorem actualWindowTCost_first : actualWindowTCost actualFirstWindow = 458745 := by
  simp only [actualWindowTCost,actualFirstWindow_count,ite_true]
theorem actualWindowTCost_batched (w : OddWindow) :
    actualWindowTCost (actualBatchedWindow w) = 514030776 := by
  simp only [actualWindowTCost,actualBatchedWindow_count]
  decide

theorem actualWindowTCost_bound (Q : Point) (hQ : order • Q = 0) :
    ∀ w ∈ actualLeftWindows ++ actualRightWindows, ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).tCount ≤ actualWindowTCost w := by
  intro w hw start history
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨i,rfl⟩) | ⟨i,rfl⟩
  · rw [actualFirstWindow_tCount start Q hQ history,actualWindowTCost_first]
  · rw [actualBatchedWindow_tCount _ start Q hQ history,actualWindowTCost_batched]
  · rw [actualBatchedWindow_tCount _ start Q hQ history,actualWindowTCost_batched]

theorem actualWindowTCost_total :
    (actualLeftWindows.map actualWindowTCost).sum +
      (actualRightWindows.map actualWindowTCost).sum = 14393320473 := by
  simp only [actualLeftWindows,actualRightWindows,List.map_cons,List.sum_cons,List.map_ofFn,
    Function.comp_def,actualWindowTCost_first,actualWindowTCost_batched]
  simp

theorem batchedOuterPlan_left : batchedOuterPlan.left.toList = actualLeftWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]
theorem batchedOuterPlan_right : batchedOuterPlan.right.toList = actualRightWindows := by
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray]

theorem batchedOuterPlan_round_t_le (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      14393374641 := by
  have h := batchedOuterPlan.round_weighted_t_le actualWindowTCost (readConstant coefficientAt Q)
    (by rw [batchedOuterPlan_left,batchedOuterPlan_right]; exact actualWindowTCost_bound Q hQ) start history
  rw [batchedOuterPlan_left,batchedOuterPlan_right,actualWindowTCost_total] at h
  exact h

theorem OuterPlan.repeat_t_le_of_round {n : Nat} (p : OuterPlan n) (cost : Nat)
    (read : ConstantBit n → Bool)
    (hcost : ∀ start history, ((p.round start).instantiate read history).tCount ≤ cost)
    (trials start : Nat) (history : Fin start → Bool) :
    ((p.repeat trials start).instantiate read history).tCount ≤ trials * cost := by
  induction trials generalizing start with
  | zero => simp [OuterPlan.repeat,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.tCount]
  | succ trials ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate]
    have ha := outer_append_t_le (p.round start) (p.repeat trials (start+p.stride)) read history
      (trials*cost) (fun h => ih _ h)
    have hb := hcost start history
    rw [Nat.succ_mul]
    omega

/-- T upper bound of the actual 6-round five-word program; includes Fourier feedback. -/
theorem batchedOuterPlan_total_t_le (Q : Point) (hQ : order • Q = 0) :
    ((batchedOuterPlan.repeat streamingRounds 0).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      86360247846 := by
  exact batchedOuterPlan.repeat_t_le_of_round 14393374641 (readConstant coefficientAt Q)
    (batchedOuterPlan_round_t_le Q hQ) streamingRounds 0 Fin.elim0

theorem batchedOuterPlan_measurements_fit :
    streamingRounds * batchedOuterPlan.stride ≤ officialLimits.measurements := by
  rw [batchedOuterPlan_finalCursor]
  decide
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WindowBudget

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.UniformT -/
section Port_UniformT

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
private theorem port_UniformT_leaf_t_zero {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (read : ConstantBit n → Bool) :
    ShorECDLP.tCount ((lookupLeafGates q ports).flatMap (TemplateGate.instantiate read)) = 0 := by
  rw [lookupLeafGates_instantiate]
  induction ports.filter (fun p => read p.1) with
  | nil => rfl
  | cons p ps ih => simpa [ShorECDLP.tCount, tCost] using ih
private theorem port_UniformT_unary_t_congr (tree : UnaryActionTree) (f g : Nat → Wire → Circuit)
    (h : ∀ l w, ShorECDLP.tCount (f l w) = ShorECDLP.tCount (g l w))
    (q : Wire) (anc : List Wire) :
    (unaryAction .inc f tree q anc).tCount = (unaryAction .inc g tree q anc).tCount := by
  induction tree generalizing q anc with
  | leaf l => simp [unaryAction,AdaptiveCircuit.tCount,h]
  | node b z o ihz iho => cases anc <;>
      simp only [unaryAction,AdaptiveCircuit.tCount,adaptive_tCount_seq,ihz,iho]
private theorem port_UniformT_field_load_uniform (field : PointField) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    ((fieldLoadProgram field start).instantiate read history).tCount = 229369 := by
  have he : ((fieldLoadProgram field start).instantiate read history).tCount =
      ((fieldLoadProgram field start).instantiate (readConstant (oddWindowCoefficients (.left 0)) 0) history).tCount := by
    simp only [fieldLoadProgram,castFinish_instantiate,lookupProgram_tCount,fieldLoadOps,unaryLookupOps_circuit]
    apply port_UniformT_unary_t_congr
    intro l w
    simp only [fieldLeaf,port_UniformT_leaf_t_zero]
  exact he.trans (fieldLoadProgram_tCount (.left 0) field start 0 (by simp) history)
private theorem port_UniformT_first_load_uniform (start : Nat)
    (read : ConstantBit 65536 → Bool) (history : Fin start → Bool) :
    ((firstLookupProgram start).instantiate read history).tCount = 458745 := by
  have he : ((firstLookupProgram start).instantiate read history).tCount =
      ((firstLookupProgram start).instantiate (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) 0) history).tCount := by
    simp only [firstLookupProgram,castFinish_instantiate,lookupProgram_tCount,firstLookupOps,unaryLookupOps_circuit]
    apply port_UniformT_unary_t_congr
    intro l w
    simp only [pointLeaf,port_UniformT_leaf_t_zero]
  exact he.trans (firstLookupProgram_tCount start 0 (by simp) history)
attribute [local irreducible] fieldLoadProgram modularAddProgram
private theorem port_UniformT_field_add_uniform (field : PointField) (acc : List Wire)
    (start : Nat) (read : ConstantBit 32768 → Bool) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) read history =
      229369 + (controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount + 229369 := by
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  let target := controlledModularAdd (List.range' 7 256) acc secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558
  have addT : ∀ h, (add.2.instantiate read h).tCount = target.tCount := by
    intro h
    exact modularAddProgram_tCount 32768 _ _ acc _ _ _ _ _ _ _
      (by simp [hl]) (by simp [secp256k1ReductionConstantBits, hl]) (by omega) read h
  have suffixT : ∀ h, compiledTCount
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩) read h =
      target.tCount + 229369 := by
    intro h
    rw [appendCompiled_tCount add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩ read h 229369
      (fun h => port_UniformT_field_load_uniform field _ read h), addT h]
  change compiledTCount
    (appendCompiled ⟨32767, fieldLoadProgram field start⟩
      (appendCompiled add ⟨32767, fieldLoadProgram field (start+32767+add.1)⟩)) read history = _
  rw [appendCompiled_tCount _ _ _ _ (target.tCount+229369) suffixT,
    port_UniformT_field_load_uniform field start read history]
  exact (Nat.add_assoc _ _ _).symm

private theorem port_UniformT_field_add_source (field : PointField) (acc : List Wire)
    (start : Nat) (read : ConstantBit 32768 → Bool) (hl : acc.length = 256)
    (history : Fin start → Bool) :
    compiledTCount (fieldLookupAddProgram field acc start) read history =
      (lookupModularAddProgram (fun l => fieldValue (windowPoint 0 (.left 0) l) field)
        pointLookupAddress pointLookupPath (List.range' 7 256) acc secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount := by
  rw [port_UniformT_field_add_uniform field acc start read hl history]
  simp only [lookupModularAddProgram, adaptive_tCount_seq]
  rw [tableLookupProgram_tCount _ _ _ _ (by decide) (by decide)]
  rfl

private theorem port_UniformT_signed_field_uniform (field : PointField) (start : Nat)
    (read : ConstantBit 32768 → Bool) (history : Fin start → Bool) :
    compiledTCount (signedFieldProgram field start) read history =
      (signedPointLookupY (fun l => fieldValue (windowPoint 0 (.left 0) l) field)).tCount := by
  unfold signedFieldProgram
  dsimp only
  unfold signedPointLookupY signedLookupModularAddProgram
  simp only [List.length_range']
  rw [adaptive_seq_assoc]
  apply appendCompiled_tCount_eq
  · exact yNegateProgram_tCount start _ history
  · intro h
    apply appendCompiled_tCount_eq
    · exact port_UniformT_field_add_source field _ _ read (by simp) h
    · intro h
      exact yNegateProgram_tCount _ _ h

theorem coordinateProgram_tCount_uniform (start : Nat) (read : ConstantBit 32768 → Bool)
    (history : Fin start → Bool) :
    compiledTCount (coordinateProgram start) read history =
      (signedLookupCoordinateProgram (fun l => fieldValue (windowPoint 0 (.left 0) l) .x)
        (fun l => fieldValue (windowPoint 0 (.left 0) l) .y)).tCount := by
  unfold coordinateProgram
  rw [← coordinateSources_eq]
  apply sequenceProgram_tCount
  unfold coordinateSegments coordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))
  · intro cursor h
    exact port_UniformT_field_add_source .negX _ cursor read (by simp) h
  · intro cursor h
    exact port_UniformT_signed_field_uniform .negY cursor read h
  · intro cursor h
    exact zeroDivisionProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact pointSquareProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact port_UniformT_field_add_source .tripleX _ cursor read (by simp) h
  · intro cursor h
    exact zeroMultiplicationProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact xNegateProgram_tCount 32768 cursor _ h
  · intro cursor h
    exact port_UniformT_field_add_source .x _ cursor read (by simp) h
  · intro cursor h
    exact port_UniformT_signed_field_uniform .negY cursor read h

attribute [local irreducible] sharedCoordinateProgram yNegateProgram placedBatchProgram
  batchedWindowCore batchedWindowPrepared signedLookupCoordinateProgram
  sharedYNegateProgram actualBatchedWindow actualLeftWindows actualRightWindows
  placedBatchSource windowYNegate sequenceCircuit batchedWindowSources

theorem sharedCoordinateProgram_tCount_uniform (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedCoordinateProgram w start) read history = 510203526 := by
  simp only [sharedCoordinateProgram,reindexCompiled,compiledTCount,reindexStraight_instantiate]
  exact (coordinateProgram_tCount_uniform start _ history).trans (coordinate_numeric_counts _ _).1

theorem batchedWindowCore_tCount_uniform (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (batchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (batchedWindowSources Q w)).tCount := by
  unfold batchedWindowCore
  apply sequenceProgram_tCount
  unfold batchedWindowSegments batchedWindowSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact (sharedCoordinateProgram_tCount_uniform w cursor _ h).trans (coordinate_numeric_counts _ _).1.symm
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h
  · intro cursor h; exact placedBatchProgram_tCount w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h


theorem actualFirstWindow_tCount_uniform (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history).tCount = 458745 := by
  simp only [actualFirstWindow,reindexStraight_instantiate]
  exact port_UniformT_first_load_uniform start _ history
theorem actualBatchedWindow_tCount_uniform (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history).tCount =
      514030776 := by
  have h := surroundCompiled_tCount (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (batchedWindowCore w 0)
    (sequenceCircuit (batchedWindowSources Q w)) (readConstant coefficientAt Q) Fin.elim0
    (batchedWindowCore_tCount_uniform w 0 Q Fin.elim0)
  simp only [AdaptiveCircuit.tCount,adaptive_tCount_seq,signedAddressCircuit_tCount,
    Nat.zero_add,Nat.add_zero,batchedWindowSources_tCount] at h
  simp only [actualBatchedWindow,closedWindow_run,relabelStraight_instantiate,AdaptiveCircuit.relabel_tCount]
  change compiledTCount (batchedWindowPrepared w 0) (readConstant coefficientAt Q) Fin.elim0 = _
  unfold batchedWindowPrepared
  exact h

theorem actualWindowTCost_bound_uniform (Q : Point) :
    ∀ w ∈ actualLeftWindows ++ actualRightWindows, ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).tCount ≤ actualWindowTCost w := by
  intro w hw start history
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨i,rfl⟩) | ⟨i,rfl⟩
  · rw [actualFirstWindow_tCount_uniform start Q history,actualWindowTCost_first]
  · rw [actualBatchedWindow_tCount_uniform _ start Q history,actualWindowTCost_batched]
  · rw [actualBatchedWindow_tCount_uniform _ start Q history,actualWindowTCost_batched]

attribute [local irreducible] batchedOuterPlan
theorem batchedOuterPlan_round_t_uniform (Q : Point)
    (start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).tCount ≤
      14393374641 := by
  have h := batchedOuterPlan.round_weighted_t_le actualWindowTCost (readConstant coefficientAt Q)
    (by rw [batchedOuterPlan_left,batchedOuterPlan_right]; exact actualWindowTCost_bound_uniform Q) start history
  rw [batchedOuterPlan_left,batchedOuterPlan_right,actualWindowTCost_total] at h
  exact h

theorem batchedOuterPlan_total_t_uniform (Q : Point) :
    ((batchedOuterPlan.repeat streamingRounds 0).instantiate (readConstant coefficientAt Q) Fin.elim0).tCount ≤
      86360247846 := by
  exact batchedOuterPlan.repeat_t_le_of_round 14393374641 (readConstant coefficientAt Q)
    (batchedOuterPlan_round_t_uniform Q) streamingRounds 0 Fin.elim0

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_UniformT

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ProductionEEASlots -/
section Port_ProductionEEASlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem schedule_layout_at {r : IndexedStepRegisters} {width first count : Nat}
    (h : IndexedScheduleLayout r width first count) (offset : Nat) (ho : offset<count) :
    IndexedStepLayout r width (first+offset) := by
  induction h generalizing offset with
  | done => omega
  | @step first count head tail ih =>
    cases offset with
    | zero => simpa using head
    | succ offset => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih offset (by omega)

theorem production_step_layout (T : Nat) (hT : 1≤T) (hmax : T≤1620) :
    IndexedStepLayout indexedStepProductionRegisters 256 T := by
  have h := schedule_layout_at secp256k1ScheduleLayout_production (T-1) (by change T-1<1620; omega)
  simpa [show 1+(T-1)=T by omega] using h

theorem endSlotBound_le (r : EndIterationRegisters) (w : EndIterationWindows)
    (hl : EndIterationLayout r 256 w) (ht : r.lengthT.length=9) :
    endSlotBound r 256 w ≤ 99900 := by
  have hu := r.upperTree_visitLabels w hl.k4_le_K4
  have hd := r.lowerTree_visitLabels 256 w hl.k5_le_decode
  rw [UnaryActionTree.visitLabels_inc] at hu hd
  have hnu := unaryAction_internalNodes_add_one (r.upperTree w)
  have hnd := unaryAction_internalNodes_add_one (r.lowerTree 256 w)
  have hlu := unaryAction_leaves_eq_labels_length (r.upperTree w)
  have hld := unaryAction_leaves_eq_labels_length (r.lowerTree 256 w)
  rw [hu] at hlu
  rw [hd] at hld
  simp only [zeroMapLabels,List.length_map,List.length_range] at hlu hld
  have hk := hl.K4_le_work
  have hk5 : w.K5Decode 256 ≤259 := Nat.min_le_right _ _
  have hr : r.lengthRP.length=9 := hl.lengthRP_length.trans ht
  have hc : r.constants.length≤9 := by
    simp only [EndIterationRegisters.constants,List.length_take,EndIterationRegisters.width,ht]
    exact Nat.min_le_left _ _
  simp only [endSlotBound,endUpperSlotBound,endLowerSlotBound,hl.work1_length,ht,hr,
    zeroMapLabels,List.length_map,List.length_range ]
  omega

theorem production_hProgram_slots (n start T : Nat)
    (hl : IndexedStepLayout indexedStepProductionRegisters 256 T) :
    (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤100000 := by
  by_cases hm : T%4=0
  · have he := endSlotBound_le _ _ (hl.endIteration hm) (by rfl)
    have hp := hProgram_slots n start indexedStepProductionRegisters 256 T
    change (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤100000
    change (hProgram n start indexedStepProductionRegisters 256 T).2.gateSlots≤
      4*9+4*9+15+endSlotBound (indexedStepProductionRegisters.endIteration 256 T) 256 (endIterationWindowsAt 256 T) at hp
    omega
  · simp only [hProgram,compiledIf_slots,if_neg hm,Straight.gateSlots]
    omega


local notation "R" => indexedStepProductionRegisters
attribute [local irreducible] blockAForward blockAInverse blockCForward blockCInverse blockDForward blockDInverse blockFForward
  intervalTree coefficientPrefixTree quotientSwapTree remainderBlockProgram coefficientBlockProgram phaseProgram
  measuredStepProgram measuredEEAForwardProgram measuredScheduleProgram primitiveResources
  canonicalWork2Rotation canonicalWork2InverseRotation terminalEpochCompression terminalWork1Clear
  measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput
  intervalProgram coefficientProgram measuredInverseStepProgram measuredEEAReverseProgram measuredInverseScheduleProgram


theorem production_blockA_length : (blockAForward R).length=2613 := by
  rw [circuit_length_primitive,blockAForward259_primitive R indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift (by simp only [indexedStepProductionRegisters,List.length_range']) (by rfl) (by rfl) (by decide)]
  rfl

theorem production_blockC_length : (blockCForward R).length=42 := by
  rw [circuit_length_primitive,blockCForward9_primitive R (by rfl) (by decide)]
  rfl

theorem production_blockF_length : (blockFForward R).length=1695 := by
  rw [blockFForward]
  rw [circuit_length_primitive,postShiftUnitary259_primitive (R).postShift indexedStepProduction_layout.postShift (by simp only [IndexedStepRegisters.postShift,indexedStepProductionRegisters,List.length_range']) (by rfl)]
  rfl

theorem production_blockD_length (T : Nat) (hl : IndexedStepLayout R 256 T) :
    (blockDForward R (certifiedActiveWindows 256 T).quotientSwap).length≤4000 := by
  let w := (certifiedActiveWindows 256 T).quotientSwap
  have hn := quotientSwapTree_nodes_le ((R).quotient w) w.start w.stop hl.quotient.k_le_K
  have hleaf := unaryAction_internalNodes_add_one (quotientSwapTree ((R).quotient w) w.start w.stop)
  have hk : w.stop≤258 := by simp only [w,certifiedActiveWindows,quotientSwapWindow]; omega
  rw [circuit_length_primitive,blockDForward9_primitive R _ hl.quotient (by rfl) (by rfl) (by decide)]
  change 48+4*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes+0+
    (170+2*(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+
    (108+(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+0≤4000
  omega

theorem production_remainderBlock_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (remainderBlockProgram n start R 256 (certifiedActiveWindows 256 T).remainder).2.gateSlots≤47000 := by
  let w := (certifiedActiveWindows 256 T).remainder
  have hn := intervalTree_nodes_le ((R).remainder w) w.start w.stop
  have h := remainderBlockProgram_slots9 n start R 256 w (by rfl) (by rfl) (by rfl) (intervalLengthQ_le_endpointScratch _ _ _ .work1 hl.remainder)
  change _≤24*9+168*(intervalTree ((R).remainder w) w.start w.stop).internalNodes+2633 at h
  have hk : w.stop=259 := rfl
  change (remainderBlockProgram n start R 256 w).2.gateSlots≤47000
  omega

theorem production_coefficientBlock_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (coefficientBlockProgram n start R 256 (certifiedActiveWindows 256 T).coefficient).2.gateSlots≤29000 := by
  let w := (certifiedActiveWindows 256 T).coefficient
  have hn := quotientSwapTree_nodes_le (((R).coefficient w).routing w.start w.stop) w.start w.stop hl.coefficient.k_le_K
  have hk : w.stop≤257 := by simp only [w,certifiedActiveWindows,coefficientWindow]; omega
  have h := coefficientBlockProgram_slots256 n start R w hl.tBoundary (by rfl)
  have hn2 : (coefficientPrefixTree ((R).coefficient w) w.start w.stop).internalNodes≤w.stop := by
    simpa only [coefficientPrefixTree] using hn
  change (coefficientBlockProgram n start R 256 w).2.gateSlots≤29000
  omega

theorem production_measuredStep_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (measuredStepProgram n start R 256 T).2.gateSlots≤200000 := by
  have hd := production_blockD_length T hl
  have h := sequenceProgram_slots_le n (measuredStepSegments n R 256 T)
    ([2613,47000,4042,29000,1695,248,100000] : List Nat) (by
      unfold measuredStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))
      · intro s; simp only [literalProgram_slots,production_blockA_length]; exact Nat.le_refl _
      · intro s; exact production_remainderBlock_slots n s T hl
      · intro s; simp only [literalProgram_slots,List.length_append,production_blockC_length]; omega
      · intro s; exact production_coefficientBlock_slots n s T hl
      · intro s; simp only [literalProgram_slots,production_blockF_length]; exact Nat.le_refl _
      · intro s; exact phaseProgram_slots n s (R).phaseUpdate (R).shiftEpoch
      · intro s; exact production_hProgram_slots n s T hl) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredStepProgram
  omega

theorem production_measuredForward_slots (n start : Nat) :
    (measuredEEAForwardProgram n start R).2.gateSlots≤324000000 := by
  have h := measuredScheduleProgram_slots_le n R 256 1620 1 200000
    (by intro T ht hmax s; exact production_measuredStep_slots n s T (production_step_layout T ht (by omega))) start
  simpa only [measuredEEAForwardProgram,secp256k1ScheduleLength] using h


theorem production_hInverseProgram_slots (n start T : Nat)
    (hl : IndexedStepLayout R 256 T) :
    (hInverseProgram n start R 256 T).2.gateSlots≤100000 := by
  by_cases hm : T%4=0
  · have he := endSlotBound_le _ _ (hl.endIteration hm) (by rfl)
    have hp := hInverseProgram_slots n start R 256 T
    change (hInverseProgram n start R 256 T).2.gateSlots≤
      4*9+4*9+15+endSlotBound ((R).endIteration 256 T) 256 (endIterationWindowsAt 256 T) at hp
    omega
  · simp only [hInverseProgram,compiledIf_slots,if_neg hm,Straight.gateSlots]
    omega

theorem production_blockAInverse_length : (blockAInverse R).length=2645 := by
  rw [circuit_length_primitive,blockAInverse259_primitive R indexedStepProduction_layout.terminalPadding
    indexedStepProduction_layout.preShift (by simp only [indexedStepProductionRegisters,List.length_range']) (by rfl) (by rfl) (by decide)]
  rfl

theorem production_blockCInverse_length : (blockCInverse R).length=42 := by
  rw [circuit_length_primitive,blockCInverse9_primitive R (by rfl) (by decide)]
  rfl

theorem production_blockDInverse_length (T : Nat) (hl : IndexedStepLayout R 256 T) :
    (blockDInverse R (certifiedActiveWindows 256 T).quotientSwap).length≤4000 := by
  let w := (certifiedActiveWindows 256 T).quotientSwap
  have hn := quotientSwapTree_nodes_le ((R).quotient w) w.start w.stop hl.quotient.k_le_K
  have hleaf := unaryAction_internalNodes_add_one (quotientSwapTree ((R).quotient w) w.start w.stop)
  have hk : w.stop≤258 := by simp only [w,certifiedActiveWindows,quotientSwapWindow]; omega
  rw [circuit_length_primitive,blockDInverse9_primitive R _ hl.quotient (by rfl) (by rfl) (by decide)]
  change 48+4*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes+0+
    (170+2*(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+
    (108+(quotientSwapTree ((R).quotient w) w.start w.stop).leaves+2*(quotientSwapTree ((R).quotient w) w.start w.stop).internalNodes)+0≤4000
  omega

theorem production_coefficient_slots (n start T : Nat) (mode : RippleMode) (sg : Bool)
    (hl : IndexedStepLayout R 256 T) :
    (coefficientProgram n start ((R).coefficient (certifiedActiveWindows 256 T).coefficient)
      (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop mode sg .work2).2.gateSlots≤14500 := by
  let w := (certifiedActiveWindows 256 T).coefficient
  have hn := quotientSwapTree_nodes_le (((R).coefficient w).routing w.start w.stop) w.start w.stop hl.coefficient.k_le_K
  have hk : w.stop≤257 := by simp only [w,certifiedActiveWindows,coefficientWindow]; omega
  have h := coefficientProgram_slots n start ((R).coefficient w) w.start w.stop mode sg .work2
  have hn2 : (coefficientPrefixTree ((R).coefficient w) w.start w.stop).internalNodes≤w.stop := by
    simpa only [coefficientPrefixTree] using hn
  change (coefficientProgram n start ((R).coefficient w) w.start w.stop mode sg .work2).2.gateSlots≤14500
  omega

theorem production_interval_slots (n start T : Nat) (mode : RippleMode) (sg : Bool)
    (hl : IndexedStepLayout R 256 T) :
    (intervalProgram n start ((R).remainder (certifiedActiveWindows 256 T).remainder) 256
      (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop mode sg .work1).2.gateSlots≤23500 := by
  let w := (certifiedActiveWindows 256 T).remainder
  have hn := intervalTree_nodes_le ((R).remainder w) w.start w.stop
  have h := intervalProgram_slots9 n start ((R).remainder w) 256 w.start w.stop mode sg .work1 (by rfl) (by rfl) (by rfl)
    (intervalLengthQ_le_endpointScratch _ _ _ .work1 hl.remainder)
  have hk : w.stop=259 := rfl
  change (intervalProgram n start ((R).remainder w) 256 w.start w.stop mode sg .work1).2.gateSlots≤23500
  omega


theorem production_measuredInverseStep_slots (n start T : Nat) (hl : IndexedStepLayout R 256 T) :
    (measuredInverseStepProgram n start R T).2.gateSlots≤200000 := by
  have hd := production_blockDInverse_length T hl
  have hp := prepareLatestPaperTBoundary_length256 (R).tBoundary hl.tBoundary (by rfl)
  have hr := restoreLatestPaperTBoundary_length256 (R).tBoundary hl.tBoundary (by rfl)
  have h1 := computeControl_length_le [(R).phase1] 1 (R).control (R).blockScratch
  have h2 := computeControl_length_le [(R).phase2,(R).sign] 2 (R).terminal (R).blockScratch
  have h3 := computeControl_length_le [(R).phase1,(R).terminal] 1 (R).control (R).blockScratch
  have h4 := rControlNonterminal_length_le [(R).phase1,(R).terminal] 0 (R).control (R).lengthRPrime ((R).blockScratch.getD 0 0) ((R).blockScratch.drop 1)
  have h5 := rControlNonterminal_length_le [(R).phase1] 0 (R).control (R).lengthRPrime (R).terminal (R).blockScratch
  have hb := blockB2_length_le R
  simp only [List.length_cons,List.length_nil] at h1 h2 h3 h4 h5
  change _≤4*9+4*2+7 at h4
  change _≤4*9+4*1+7 at h5
  change _≤8*9+31 at hb
  have h := sequenceProgram_slots_le n (measuredInverseStepSegments n R T)
    ([100000,248,1929,14500,33,14500,4500,23500,210,23500,2700] : List Nat) (by
      unfold measuredInverseStepSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))))))
      · intro s; exact production_hInverseProgram_slots n s T hl
      · intro s; exact phaseInverseProgram_slots n s (R).phaseUpdate (R).shiftEpoch
      · intro s; simp only [literalProgram_slots,List.length_append,circuit_adjoint_length,production_blockF_length]; omega
      · intro s; exact production_coefficient_slots n s T (RippleMode.add.inverse) true hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact production_coefficient_slots n s T (RippleMode.sub.inverse) false hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil,production_blockCInverse_length]; omega
      · intro s; exact production_interval_slots n s T (RippleMode.add.inverse) false hl
      · intro s; simp only [literalProgram_slots,List.length_append,List.length_cons,List.length_nil]; omega
      · intro s; exact production_interval_slots n s T (RippleMode.sub.inverse) true hl
      · intro s; simp only [literalProgram_slots,List.length_append,production_blockAInverse_length]; omega) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredInverseStepProgram
  omega

theorem production_measuredReverse_slots (n start : Nat) :
    (measuredEEAReverseProgram n start R).2.gateSlots≤324000000 := by
  have h := measuredInverseScheduleProgram_slots_le n R 1620 1 200000
    (by intro T ht hmax s; exact production_measuredInverseStep_slots n s T (production_step_layout T ht (by omega))) start
  simpa only [measuredEEAReverseProgram,secp256k1ScheduleLength] using h


theorem constMinusProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length=dirty.length+1) (hk : bits.length=input.length) :
    (constMinusProgram n start input dirty bits q c r t).2.gateSlots≤53*input.length := by
  have hi := gidneyProgram_slots_le n start input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t hd (by simp)
  have hb (s : Nat) := gidneyProgram_slots_le n s input dirty bits q c r t hd hk
  simp only [constMinusProgram,prependCompiled_slots,appendCompiled_slots,controlledComplement,List.length_map]
  grind only

theorem eeaCenterProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length) (hk : bits.length=input.length)
    (hp : 0 < input.length) :
    (eeaCenterProgram n start input dirty bits p c r t iter).2.gateSlots≤78*input.length+1 := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by simp only [List.length_take,← hd]; omega
  have hc := uncontrolledCompareProgram_slots_le n start input dirty (p/2+1) c r t iter hd
  have hn (s : Nat) := constMinusProgram_slots n s input (dirty.take (input.length-1)) bits iter c r t ht hk
  simp only [eeaCenterProgram,appendCompiled_slots]
  grind only

theorem eeaUncenterProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length) (hk : bits.length=input.length)
    (hp : 0 < input.length) :
    (eeaUncenterProgram n start input dirty bits p c r t iter).2.gateSlots≤78*input.length+1 := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by simp only [List.length_take,← hd]; omega
  have hn := constMinusProgram_slots n start input (dirty.take (input.length-1)) bits iter c r t ht hk
  have hc (s : Nat) := uncontrolledCompareProgram_slots_le n s input dirty (p/2+1) c r t iter hd
  simp only [eeaUncenterProgram,appendCompiled_slots]
  grind only

theorem eeaParityProgram_slots (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length=dirty.length+1) (hk : bits.length=input.length) :
    (eeaParityProgram n start input dirty bits c r t iter).2.gateSlots≤53*input.length+2 := by
  have h := constMinusProgram_slots n start input dirty bits iter c r t hd hk
  simp only [eeaParityProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem preprocessProgram_slots (n start : Nat) : (preprocessProgram n start).2.gateSlots≤600000 := by
  have hc := eeaCenterProgram_slots n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp) (by simp)
  have hp : workRegistersPrepare.length=641 := by rw [circuit_length_primitive,workRegistersPrepare_primitive]; rfl
  have hl : eeaLengthSetup.length=518649 := by rw [circuit_length_primitive,eeaLengthSetup_primitive]; rfl
  simp only [List.length_reverse,List.length_range'] at hc
  simp only [preprocessProgram,surroundCompiled_slots,hp,hl]
  omega

theorem unpreprocessProgram_slots (n start : Nat) : (unpreprocessProgram n start).2.gateSlots≤600000 := by
  have hc := eeaUncenterProgram_slots n start (List.range' 266 256).reverse (List.range' 4 256)
    (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2 (by simp) (by simp) (by simp)
  have hp : workRegistersRestore.length=641 := by rw [circuit_length_primitive,workRegistersRestore_primitive]; rfl
  have hl : eeaLengthUndo.length=518649 := by rw [circuit_length_primitive,eeaLengthUndo_primitive]; rfl
  simp only [List.length_reverse,List.length_range'] at hc
  simp only [unpreprocessProgram,surroundCompiled_slots,hp,hl]
  omega

theorem productionParityProgram_slots (n start : Nat) : (productionParityProgram n start).2.gateSlots≤13570 := by
  have h := eeaParityProgram_slots n start (List.range' 263 256) (List.range' 4 255) secp256k1ModulusBits 560 561 562 2 (by simp) (by simp [secp256k1ModulusBits])
  simpa only [List.length_range'] using h


theorem canonicalWork2Rotation_length : canonicalWork2Rotation.length=7866 := by
  rw [circuit_length_primitive,canonicalWork2Rotation_primitive]; rfl

theorem canonicalWork2InverseRotation_length : canonicalWork2InverseRotation.length=7866 := by
  rw [circuit_length_primitive,canonicalWork2InverseRotation_primitive]; rfl

theorem terminalEpochCompression_length : terminalEpochCompression.length=25 := by
  rw [circuit_length_primitive,terminalEpochCompression_primitive]; rfl

theorem terminalWork1Clear_length : terminalWork1Clear.length=251 := by
  rw [circuit_length_primitive,terminalWork1Clear_primitive]; rfl

theorem measuredForwardWrapperProgram_slots (n start : Nat) :
    (measuredForwardWrapperProgram n start).2.gateSlots≤325000000 := by
  have h := sequenceProgram_slots_le n (measuredForwardWrapperSegments n)
    ([600000,324000000,7891,13570,251] : List Nat) (by
      unfold measuredForwardWrapperSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; exact preprocessProgram_slots n s
      · intro s; exact production_measuredForward_slots n s
      · intro s; simp only [literalProgram_slots,List.length_append,canonicalWork2Rotation_length,terminalEpochCompression_length]; decide
      · intro s; exact productionParityProgram_slots n s
      · intro s; simp only [literalProgram_slots,terminalWork1Clear_length]; decide) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredForwardWrapperProgram
  omega

theorem measuredReverseWrapperProgram_slots (n start : Nat) :
    (measuredReverseWrapperProgram n start).2.gateSlots≤325000000 := by
  have h := sequenceProgram_slots_le n (measuredReverseWrapperSegments n)
    ([251,13570,7891,324000000,600000] : List Nat) (by
      unfold measuredReverseWrapperSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
      · intro s; simp only [literalProgram_slots,terminalWork1Clear_length]; decide
      · intro s; exact productionParityProgram_slots n s
      · intro s; simp only [literalProgram_slots,List.length_append,canonicalWork2InverseRotation_length,terminalEpochCompression_length]; decide
      · intro s; exact production_measuredReverse_slots n s
      · intro s; exact unpreprocessProgram_slots n s) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold measuredReverseWrapperProgram
  omega



end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ProductionEEASlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.InPlaceSlots -/
section Port_InPlaceSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] measuredForwardWrapperProgram measuredReverseWrapperProgram
  hornerProgram hornerInverseProgram multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram fig15SwapOutput
theorem collectProgram_slots_le (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (bound : Nat) (h : ∀ cursor prior, (next cursor prior).2.gateSlots≤bound)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    (collectProgram n next ws start prior).2.gateSlots≤bound := by
  induction ws generalizing start with
  | nil => exact h start prior
  | cons w ws ih =>
    simp only [collectProgram,castFinish_gateSlots,Straight.gateSlots]
    exact ih _ _

theorem relabelCompiled_slots {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    (relabelCompiled e p).2.gateSlots=p.2.gateSlots := by
  exact relabelStraight_slots e p.2

attribute [local irreducible] relabelCompiled measuredForwardDataBankProgram measuredReverseDataBankProgram
  divisionCleanupProgram divisionCorrectionProgram divisionAfterResetProgram divisionProgram
  multiplicationCleanupProgram multiplicationCorrectionProgram multiplicationAfterResetProgram multiplicationProgram

theorem measuredForwardDataBankProgram_slots (n start : Nat) :
    (measuredForwardDataBankProgram n start).2.gateSlots≤325000000 := by
  simp only [measuredForwardDataBankProgram,relabelCompiled_slots]
  exact measuredForwardWrapperProgram_slots n start

theorem measuredReverseDataBankProgram_slots (n start : Nat) :
    (measuredReverseDataBankProgram n start).2.gateSlots≤325000000 := by
  simp only [measuredReverseDataBankProgram,relabelCompiled_slots]
  exact measuredReverseWrapperProgram_slots n start

theorem correctionCompiled_slots_le (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    (correctionCompiled n start ws prior).2.gateSlots≤3*ws.length := by
  simp only [correctionCompiled,registerCorrectionProgram_slots,Straight.gateSlots]
  omega

theorem appendLiteral_slots {n start : Nat} (p : (count : Nat) × Straight n start (start+count)) (gs : Circuit) :
    (appendLiteral p gs).2.gateSlots=p.2.gateSlots+gs.length := by
  simp only [appendLiteral,appendCompiled_slots,literalProgram_slots]

theorem fig15SwapOutput_length : fig15SwapOutput.length=768 := by
  rw [circuit_length_primitive,fig15SwapOutput_primitive]; rfl

theorem multiplyWorkProgram_slots (n start : Nat) : (multiplyWorkProgram n start).2.gateSlots≤8000000 := by
  have h := hornerProgram_slots256 n start (List.range' 263 256) (List.range' 580 256) (List.range' 7 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
  simp only [List.length_range'] at h
  unfold multiplyWorkProgram
  omega

theorem multiplyDataProgram_slots (n start : Nat) : (multiplyDataProgram n start).2.gateSlots≤8000000 := by
  have h := hornerProgram_slots256 n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp [secp256k1ReductionConstantBits])
  simp only [List.length_range'] at h
  unfold multiplyDataProgram
  omega

theorem unmultiplyDataProgram_slots (n start : Nat) : (unmultiplyDataProgram n start).2.gateSlots≤8000000 := by
  have h := hornerInverseProgram_slots256 n start (List.range' 263 256) (List.range' 7 256) (List.range' 580 256) (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559 (by simp) (by simp) (by simp)
  simp only [List.length_range'] at h
  unfold unmultiplyDataProgram
  omega

theorem divisionCorrectionProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (divisionCorrectionProgram n start prior).2.gateSlots≤8001536 := by
  have hc := correctionCompiled_slots_le n start (List.range' 580 256) prior
  have hm := unmultiplyDataProgram_slots n start
  simp only [List.length_range'] at hc
  simp only [divisionCorrectionProgram,divisionCleanupProgram,appendCompiled_slots,appendLiteral_slots,fig15SwapOutput_length]
  omega

theorem divisionAfterResetProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (divisionAfterResetProgram n start prior).2.gateSlots≤341001536 := by
  have he := measuredReverseDataBankProgram_slots n start
  have hm (s : Nat) := multiplyDataProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := divisionCorrectionProgram_slots n s p
  simp only [divisionAfterResetProgram,appendRetaining,appendCompiled_slots]
  grind only

theorem divisionProgram_slots (n start : Nat) : (divisionProgram n start).2.gateSlots≤675000000 := by
  have he := measuredForwardWrapperProgram_slots n start
  have hm (s : Nat) := multiplyWorkProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := collectProgram_slots_le n (divisionAfterResetProgram n)
    341001536 (divisionAfterResetProgram_slots n) (List.range' 580 256) s p
  simp only [divisionProgram,appendCompiled_slots]
  grind only

theorem multiplicationCorrectionProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (multiplicationCorrectionProgram n start prior).2.gateSlots≤333001536 := by
  have hc := correctionCompiled_slots_le n start (List.range' 580 256) prior
  have hm := unmultiplyDataProgram_slots n start
  have he (s : Nat) := measuredReverseDataBankProgram_slots n s
  simp only [List.length_range'] at hc
  simp only [multiplicationCorrectionProgram,multiplicationCleanupProgram,appendCompiled_slots,appendLiteral_slots,fig15SwapOutput_length]
  grind only

theorem multiplicationAfterResetProgram_slots (n start : Nat) (prior : List (Fin start)) :
    (multiplicationAfterResetProgram n start prior).2.gateSlots≤666001536 := by
  have he := measuredForwardDataBankProgram_slots n start
  have hm (s : Nat) := multiplyDataProgram_slots n s
  have hc (s : Nat) (p : List (Fin s)) := multiplicationCorrectionProgram_slots n s p
  simp only [multiplicationAfterResetProgram,appendRetaining,appendCompiled_slots]
  grind only

theorem multiplicationProgram_slots (n start : Nat) : (multiplicationProgram n start).2.gateSlots≤675000000 := by
  have hm := multiplyWorkProgram_slots n start
  have hc (s : Nat) (p : List (Fin s)) := collectProgram_slots_le n (multiplicationAfterResetProgram n)
    666001536 (multiplicationAfterResetProgram_slots n) (List.range' 580 256) s p
  simp only [multiplicationProgram,appendCompiled_slots]
  grind only


end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_InPlaceSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowSlots -/
section Port_WindowSlots

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] divisionProgram multiplicationProgram
attribute [local irreducible] zeroDivisionProgram zeroMultiplicationProgram modularNegateProgram squareSubtractProgram coordinateProgram

theorem fig15ZeroPrepare_length : fig15ZeroPrepare.length=1022 := by
  rw [circuit_length_primitive,fig15ZeroPrepare_primitive]; rfl

theorem fig15ZeroRestore_length : fig15ZeroRestore.length=1022 := by
  rw [circuit_length_primitive,fig15ZeroRestore_primitive]; rfl

theorem zeroDivisionProgram_slots (n start : Nat) :
    (zeroDivisionProgram n start).2.gateSlots≤676000000 := by
  have h := divisionProgram_slots n start
  simp only [zeroDivisionProgram,surroundCompiled_slots,fig15ZeroPrepare_length,fig15ZeroRestore_length]
  omega

theorem zeroMultiplicationProgram_slots (n start : Nat) :
    (zeroMultiplicationProgram n start).2.gateSlots≤676000000 := by
  have h := multiplicationProgram_slots n start
  simp only [zeroMultiplicationProgram,surroundCompiled_slots,fig15ZeroPrepare_length,fig15ZeroRestore_length]
  omega

theorem xNegateProgram_slots (n start : Nat) :
    (xNegateProgram n start).2.gateSlots≤26370 := by
  have h := modularNegateProgram_slots_le n start (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558 (by simp) (by simp) (by simp)
  simpa only [List.length_range'] using h

theorem pointSquareProgram_slots (n start : Nat) :
    (pointSquareProgram n start).2.gateSlots≤15750663 := by
  exact squareSubtractProgram_slots256 n start _ _ _ _ _ _ _ _ _ _ _ _
    (by simp) (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) (by simp)

theorem coordinateProgram_slots (start : Nat) :
    (coordinateProgram start).2.gateSlots≤1500000000 := by
  have h := sequenceProgram_slots_le 32768 coordinateSegments
    ([17449459,17502203,676000000,15750663,17449459,676000000,26370,17449459,17502203] : List Nat) (by
      unfold coordinateSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))))))
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s
      · intro s; exact zeroDivisionProgram_slots _ s
      · intro s; exact pointSquareProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact zeroMultiplicationProgram_slots _ s
      · intro s; exact xNegateProgram_slots _ s
      · intro s; exact fieldLookupAddProgram_slots _ _ s (by simp)
      · intro s; exact signedFieldProgram_slots _ s) start
  simp only [List.sum_cons,List.sum_nil] at h
  unfold coordinateProgram
  omega


theorem reindexCompiled_slots {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    (reindexCompiled f p).2.gateSlots=p.2.gateSlots := by
  exact reindexStraight_gateSlots f p.2

attribute [local irreducible] reindexCompiled sharedCoordinateProgram sharedYNegateProgram
  placedBatchProgram batchedWindowCore batchedWindowPrepared actualBatchedWindow actualFirstWindow
  actualLeftWindows actualRightWindows batchedOuterPlan

theorem sharedCoordinateProgram_slots (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).2.gateSlots≤1500000000 := by
  simp only [sharedCoordinateProgram,reindexCompiled_slots]
  exact coordinateProgram_slots start

theorem sharedYNegateProgram_slots (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).2.gateSlots≤26372 := by
  simp only [sharedYNegateProgram,reindexCompiled_slots]
  exact yNegateProgram_slots_le start

theorem batchedWindowCore_slots (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).2.gateSlots≤2683845980 := by
  have h := sequenceProgram_slots_le 983040 (batchedWindowSegments w)
    ([1500000000,26372,1183793236,26372] : List Nat) (by
      unfold batchedWindowSegments
      refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
      · intro s; exact sharedCoordinateProgram_slots w s
      · intro s; exact sharedYNegateProgram_slots w s
      · intro s; exact placedBatchProgram_slots w s
      · intro s; exact sharedYNegateProgram_slots w s) start
  simpa only [batchedWindowCore,List.sum_cons,List.sum_nil] using h

theorem batchedWindowPrepared_slots (w : OddWindow) (start : Nat) :
    (batchedWindowPrepared w start).2.gateSlots≤3000000000 := by
  have h := batchedWindowCore_slots w start
  simp only [batchedWindowPrepared,surroundCompiled_slots,signedAddressCircuit_length,
    pointLookupAddress,List.length_range']
  omega

theorem actualBatchedWindow_slots (w : OddWindow) (start : Nat) :
    ((actualBatchedWindow w).program start).gateSlots≤3000000000 := by
  simp only [actualBatchedWindow,closedWindow,shiftStraight_gateSlots,relabelStraight_slots]
  exact batchedWindowPrepared_slots w 0

theorem batchedOuterPlan_windowSlots :
    ∀ w ∈ batchedOuterPlan.left.toList ++ batchedOuterPlan.right.toList,
      ∀ start, (w.program start).gateSlots≤3000000000 := by
  intro w hw start
  simp only [batchedOuterPlan,standardOuterPlan,Vector.toList,List.toList_toArray,
    actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨i,rfl⟩) | ⟨i,rfl⟩
  · exact (actualFirstWindow_slots start).trans (by decide)
  · exact actualBatchedWindow_slots _ start
  · exact actualBatchedWindow_slots _ start

/-- Syntactic slots of the actual 6-round program. This counts every fixed
correction slot; it does not assert physical validity, success, or wire support. -/
theorem batchedOuterPlan_slots (start : Nat) :
    (batchedOuterPlan.repeat streamingRounds start).gateSlots≤5000000000000 := by
  exact (batchedOuterPlan.repeat_slots_le 3000000000 batchedOuterPlan_windowSlots streamingRounds start).trans (by decide)


end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WindowSlots

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ResourceCertificate -/
section Port_ResourceCertificate

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
attribute [local irreducible] batchedOuterPlan coefficientTable OuterPlan.repeat

/-- Generic packaging avoids unfolding a large coefficient table to transport its length. -/
def fixedTableEntry {n e : Nat} (f : Fin n → PointCoeff) (p : Straight n 0 e) : StraightEntry where
  coefficients := List.ofFn f
  finalCursor := e
  program := reindexStraight (Fin.cast List.length_ofFn.symm) p

private theorem port_ResourceCertificate_ofFn_read {n : Nat} (f : Fin n → PointCoeff) (Q : Point) :
    (fun r : ConstantBit n => readConstant (List.ofFn f).get Q
      ⟨Fin.cast (List.length_ofFn).symm r.point, r.field, r.bit⟩) =
      readConstant f Q := by
  funext r
  simp only [readConstant,List.get_eq_getElem,List.getElem_ofFn,Fin.val_cast,Fin.eta]

theorem fixedTableEntry_instantiate {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (fixedTableEntry f p).instantiate Q = p.instantiate (readConstant f Q) Fin.elim0 := by
  dsimp only [fixedTableEntry,StraightEntry.instantiate]
  rw [reindexStraight_instantiate]
  simp only [Function.comp_def,reindexBit]
  rw [port_ResourceCertificate_ofFn_read]

theorem fixedTableEntry_slots {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).program.gateSlots = p.gateSlots :=
  reindexStraight_gateSlots _ _

theorem fixedTableEntry_wellFormed {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).program.WellFormed ↔ p.WellFormed :=
  reindexStraight_wellFormed _ _

theorem fixedTableEntry_cursor {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).finalCursor = e := rfl

theorem fixedTableEntry_rows {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) : (fixedTableEntry f p).coefficients.length = n := List.length_ofFn

private theorem port_ResourceCertificate_resource_t (c : AdaptiveCircuit) : (resources c).tModel = c.tCount := rfl
private theorem port_ResourceCertificate_resource_m (c : AdaptiveCircuit) : (resources c).measurements = c.measurementCount := rfl
private theorem port_ResourceCertificate_resource_q (c : AdaptiveCircuit) : (resources c).qubits = c.qubitCount := rfl

theorem fixedTableEntry_measurements {n e : Nat} (f : Fin n → PointCoeff)
    (p : Straight n 0 e) (Q : Point) :
    (resources ((fixedTableEntry f p).instantiate Q)).measurements = e := by
  rw [port_ResourceCertificate_resource_m,fixedTableEntry_instantiate,Straight.measurementCount,Nat.sub_zero]

/-- The actual fixed 6-round producer, using the public coefficient table. -/
def streamingEntry : StraightEntry := fixedTableEntry coefficientAt (batchedOuterPlan.repeat streamingRounds 0)

theorem streamingEntry_instantiate (Q : Point) :
    streamingEntry.instantiate Q =
      (batchedOuterPlan.repeat streamingRounds 0).instantiate (readConstant coefficientAt Q) Fin.elim0 :=
  fixedTableEntry_instantiate _ _ Q

attribute [local irreducible] streamingEntry fixedTableEntry

/-- Upper bounds; the qubit bound is not an exact cardinality claim. -/
def streamingBounds : Bounds := ⟨3932,86360247846,5163644892⟩

theorem streamingEntry_qubitCount (Q : Point) :
    (streamingEntry.instantiate Q).qubitCount ≤ 3932 := by
  rw [streamingEntry_instantiate]
  simpa only [AdaptiveCircuit.qubitCount,List.card_toFinset] using
    batchedOuter_qubits_le_3932 streamingRounds 0 (readConstant coefficientAt Q) Fin.elim0

theorem streamingEntry_tModel (Q : Point) :
    (resources (streamingEntry.instantiate Q)).tModel ≤ 86360247846 := by
  rw [port_ResourceCertificate_resource_t,streamingEntry_instantiate]
  exact batchedOuterPlan_total_t_uniform Q

theorem streamingEntry_measurements (Q : Point) :
    (resources (streamingEntry.instantiate Q)).measurements = 5163644892 := by
  rw [streamingEntry,fixedTableEntry_measurements,Nat.zero_add]
  exact batchedOuterPlan_finalCursor

theorem streamingEntry_resources (Q : Point) :
    (resources (streamingEntry.instantiate Q)).qubits ≤ streamingBounds.qubits ∧
    (resources (streamingEntry.instantiate Q)).tModel ≤ streamingBounds.tModel ∧
    (resources (streamingEntry.instantiate Q)).measurements ≤ streamingBounds.measurements := by
  rw [port_ResourceCertificate_resource_q]
  exact ⟨streamingEntry_qubitCount Q,streamingEntry_tModel Q,(streamingEntry_measurements Q).le⟩

theorem streamingEntry_gateSlots : streamingEntry.program.gateSlots ≤ 5000000000000 := by
  simpa only [streamingEntry,fixedTableEntry_slots] using batchedOuterPlan_slots 0

theorem streamingEntry_gateBudget : streamingEntry.program.gateSlots ≤ officialLimits.gateSlots :=
  streamingEntry_gateSlots.trans (by decide)

theorem streamingEntry_finalCursor : streamingEntry.finalCursor = 5163644892 := by
  unfold streamingEntry
  exact (fixedTableEntry_cursor coefficientAt (batchedOuterPlan.repeat streamingRounds 0)).trans
    ((Nat.zero_add _).trans batchedOuterPlan_finalCursor)

theorem streamingEntry_recordBudget : streamingEntry.finalCursor ≤ officialLimits.measurements :=
  streamingEntry_finalCursor.le.trans (by decide)

theorem streamingEntry_tableBudget : streamingEntry.coefficients.length ≤ officialLimits.coefficientRows := by
  rw [streamingEntry,fixedTableEntry_rows]
  exact Nat.le_refl _

theorem streamingEntry_candidateBudget :
    batchedOuterPlan.layoutForStreaming.trials.length *
      decoderCandidateLimit batchedOuterPlan.layoutForStreaming.kind batchedOuterPlan.layoutForStreaming.params ≤
      officialLimits.candidateChecks := by
  exact streaming_candidate_budget batchedOuterPlan.layoutForStreaming rfl rfl

theorem streamingEntry_wellFormed : streamingEntry.program.WellFormed := by
  rw [streamingEntry]
  exact (fixedTableEntry_wellFormed _ _).mpr (batchedOuterPlan_repeat_wellFormed streamingRounds 0)

/-- Only success remains an input: all physical, syntactic and resource fields
refer to this actual fixed entry. This conditional shell is not an accepted submission. -/
theorem streamingEntry_certificate
    (success : ∀ (Q : Point) (d : Nat), Q ≠ 0 → Q = d • G →
      (99 : ℝ)/100 ≤ Instrument.bornMass
        ((streamingEntry.instantiate Q).run.filter
          (fun b => (verifiedCandidate batchedOuterPlan.layoutForStreaming Q b.history).isSome))
        (ket zeroBasisState)) :
    Certificate officialLimits batchedOuterPlan.layoutForStreaming streamingEntry streamingBounds where
  gateBudget := streamingEntry_gateBudget
  recordBudget := streamingEntry_recordBudget
  tableBudget := streamingEntry_tableBudget
  candidateBudget := streamingEntry_candidateBudget
  wellFormed := streamingEntry_wellFormed
  resources := streamingEntry_resources
  success := success
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ResourceCertificate

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.RoundBoundary -/
section Port_RoundBoundary

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] streamAddress fourierOutcomes actualFirstSource actualOddSource fourierBranch Quantum.run
private theorem port_RoundBoundary_smul_support {V : BasisState → Prop} (c : ℂ) {ψ : State}
    (h : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply h s
  intro he
  exact hs (by simp [he])

/-- Continuation composition preserves reached-state predicates branch by branch. -/
theorem streamBlockContinuation_supported {V W : BasisState → Prop}
    (call : AdaptiveCircuit) (prior : List Bool) (next : List Bool → Instrument)
    (hcall : ∀ b ∈ call.run, ∀ ψ, SupportedOn V ψ → SupportedOn BatchedWindowValid (b.kraus ψ))
    (hnext : ∀ bits b, b ∈ next bits → ∀ ψ, SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn V (Quantum.run (streamAddress.map Gate.H) ψ))
    (b : InstrumentBranch) (hb : b ∈ streamBlockContinuation call prior next) :
    SupportedOn W (b.kraus ψ) := by
  rw [streamBlockContinuation_eq] at hb
  have hu : (AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).run =
      [⟨List.nil, Quantum.run (streamAddress.map Gate.H)⟩] := AdaptiveCircuit.run_unitary_done _
  rw [hu] at hb
  simp only [Instrument.seq,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hb
  obtain ⟨bc,hbc,rfl⟩ := List.mem_map.mp hb
  obtain ⟨c,hc,hmap⟩ := List.mem_flatMap.mp hbc
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hmap
  rw [fourierContinuationInstrument] at hf
  obtain ⟨bits,hbits,hfm⟩ := List.mem_flatMap.mp hf
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hfm
  change SupportedOn W (d.kraus (fourierBranch .inverse streamAddress.reverse prior bits
    (c.kraus (Quantum.run (streamAddress.map Gate.H) ψ))))
  exact hnext bits d hd _ (batchedWindowValid_fourierBranch .inverse streamAddress.reverse
    (fun w hw => List.mem_reverse.mp hw) prior bits _ (hcall c hc _ hψ))

theorem actualSourceAxis_supported (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (ws : List OddWindow) (prior : List Bool) (next : List Bool → Instrument)
    (W : BasisState → Prop)
    (hnext : ∀ bits b, b ∈ next bits → ∀ ψ, SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ)
    (b : InstrumentBranch) (hb : b ∈ selectedSourceAxis (actualOddSource Q) ws prior next) :
    SupportedOn W (b.kraus ψ) := by
  induction ws generalizing prior ψ b with
  | nil => exact hnext prior b hb ψ hψ
  | cons w ws ih =>
    apply streamBlockContinuation_supported (V := BatchedWindowValid) (W := W) (actualOddSource Q w) prior _ ?_ ?_ ψ
      (batchedWindowValid_prepare _ (fun _ h => h) ψ hψ) b hb
    · intro c hc φ hφ
      obtain ⟨a,ha⟩ := (actualOddSource_coherent Q hQ hn w).branch_coefficient c hc
      rw [ha.on_supported hφ]
      exact port_RoundBoundary_smul_support a (actualBatchedWindowState_supported Q hQ hn w φ hφ)
    · intro bits c hc φ hφ
      exact ih _ φ hφ c hc

theorem actualSourceTwoAxes_supported (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (left right : List OddWindow) (next : List Bool → List Bool → Instrument)
    (W : BasisState → Prop)
    (hnext : ∀ lhs rhs b, b ∈ next lhs rhs → ∀ ψ,
      SupportedOn BatchedWindowValid ψ → SupportedOn W (b.kraus ψ))
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ)
    (b : InstrumentBranch)
    (hb : b ∈ selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right next) :
    SupportedOn W (b.kraus ψ) := by
  apply streamBlockContinuation_supported (V := FirstWindowInput) (W := W)
    (actualFirstSource Q) List.nil _ ?_ ?_ ψ
    (firstWindowInput_prepare _ (fun _ h => h) ψ hψ) b hb
  · intro c hc φ hφ
    obtain ⟨a,ha⟩ := (actualFirstSource_coherent_input Q hQ).branch_coefficient c hc
    rw [ha.on_supported hφ]
    exact port_RoundBoundary_smul_support a (actualFirstWindowState_supported Q φ hφ)
  · intro bits c hc φ hφ
    apply actualSourceAxis_supported Q hQ hn left bits.reverse _ W ?_ φ hφ c hc
    intro lhs d hd χ hχ
    exact actualSourceAxis_supported Q hQ hn right List.nil _ W (hnext lhs) χ hχ d hd

theorem batchedReset_flag_absent : 837 ∉ batchedResetWires := by
  simp [batchedResetWires,resetWires]

theorem actualRoundTail_zeroFlag (b : InstrumentBranch)
    (hb : b ∈ (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn (fun s => s 837=false) (b.kraus ψ) := by
  refine AdaptiveCircuit.branch_frame _ 837 false ?_ b hb ψ ?_
  · simp only [AdaptiveCircuit.wires,List.mem_append,not_or]
    constructor
    · simp [circuitWires,gateWires]
    · intro h
      exact batchedReset_flag_absent (resetRegister_support _ h)
  · intro s hs
    exact (hψ s hs).1.1.1.2.1

theorem actualAxesTail_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (left right : List OddWindow) (b : InstrumentBranch)
    (hb : b ∈ selectedSourceTwoAxes (actualFirstSource Q) (actualOddSource Q) left right
      (fun _ _ => (AdaptiveCircuit.unitary [.X 836]
        (measureResetWithCorrection batchedResetWires (fun _ => []))).run)) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket (zeroBasisState[836 ↦ true]))) := by
  exact actualSourceTwoAxes_supported Q hQ hn left right _ _
    (fun _ _ => actualRoundTail_zeroFlag) _
    (supportedOn_ket _ _ firstWindowInput_start) b hb

theorem actualRoundSource_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket zeroBasisState)) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,actualLeftSources_indices,actualRightSources_indices] at hb
  rw [AdaptiveCircuit.run, ← selectedSourceTwoAxes_constant] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  change SupportedOn (fun s => s 837=false) (c.kraus (Quantum.run [.X 836] (ket zeroBasisState)))
  rw [hx]
  exact actualAxesTail_zeroFlag Q hQ hn leftOddIndices rightOddIndices c hc

theorem actualCompiledRound_zeroFlag (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    SupportedOn (fun s => s 837=false) (b.kraus (ket zeroBasisState)) := by
  rw [batchedOuterPlan_round_run Q hQ start history] at hb
  exact actualRoundSource_zeroFlag Q hQ hn b hb
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_RoundBoundary

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.RoundReset -/
section Port_RoundReset

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] actualFirstSource actualOddSource streamAddress fourierOutcomes Quantum.run batchedOuterPlan actualFirstWindow actualBatchedWindow

theorem batchedResetWires_nodup : batchedResetWires.Nodup := by
  simp only [batchedResetWires,resetWires,List.nodup_append,List.nodup_range,
    List.nodup_range' 1, List.nodup_singleton,true_and]
  simp only [List.mem_append,List.mem_range,List.mem_range'_1,List.mem_singleton]
  repeat' constructor
  all_goals intros; dsimp only [Wire] at *; omega

theorem actualRound_support (start : Nat) (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate read history).wires ⊆ completeBatchedSupport := by
  apply OuterPlan.round_support
  · intro w hw
    simp only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.mem_reverse] at hw
    exact List.mem_cons_of_mem 837 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw)))
  · simpa only [batchedOuterPlan,standardOuterPlan] using
      (List.subset_cons_of_subset 837 (List.Subset.refl batchedResetWires))
  · simp [completeBatchedSupport,batchedResetWires,resetWires]
  · intro window hw cursor h
    apply (straight_instantiate_support _ read h).trans
    apply actualWindows_support_static window _ cursor
    simpa only [batchedOuterPlan,standardOuterPlan,Vector.toList_mk,List.toList_toArray] using hw

theorem actualRoundTail_clean (b : InstrumentBranch)
    (hb : b ∈ (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run) (ψ : State) :
    SupportedOn (Clean batchedResetWires) (b.kraus ψ) := by
  rw [AdaptiveCircuit.run] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  exact resetRegister_clean _ batchedResetWires_nodup c hc _

theorem actualRoundSource_clean (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    SupportedOn (Clean batchedResetWires) (b.kraus (ket zeroBasisState)) := by
  rw [actualRoundSource,sourceOuterRound_streamAxis,actualLeftSources_indices,actualRightSources_indices] at hb
  rw [AdaptiveCircuit.run, ← selectedSourceTwoAxes_constant] at hb
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
  have hx : Quantum.run [.X 836] (ket zeroBasisState) = ket (zeroBasisState[836 ↦ true]) := by
    simp [Quantum.run,applyGate_ket,onKet,zeroBasisState]
  change SupportedOn (Clean batchedResetWires) (c.kraus (Quantum.run [.X 836] (ket zeroBasisState)))
  rw [hx]
  exact actualSourceTwoAxes_supported Q hQ hn leftOddIndices rightOddIndices _ _
    (fun _ _ b hb ψ _ => actualRoundTail_clean b hb ψ) _
    (supportedOn_ket _ _ firstWindowInput_start) c hc

theorem actualCompiledRound_zero_support (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    SupportedOn (fun s => s=zeroBasisState) (b.kraus (ket zeroBasisState)) := by
  intro s hs
  funext w
  by_cases hw : w ∈ batchedResetWires
  · have hb' := hb
    rw [batchedOuterPlan_round_run Q hQ start history] at hb'
    exact actualRoundSource_clean Q hQ hn b hb' s hs w hw
  · by_cases he : w=837
    · subst w
      exact actualCompiledRound_zeroFlag Q hQ hn start history b hb s hs
    · exact AdaptiveCircuit.branch_frame _ w false
        (fun h => (List.mem_cons.mp (actualRound_support start _ history h)).elim he hw)
        b hb (ket zeroBasisState) (supportedOn_ket _ _ rfl) s hs

theorem actualCompiledRound_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  supportedZero_scalar _ (actualCompiledRound_zero_support Q hQ hn start history b hb)

theorem actualRoundSource_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  apply actualCompiledRound_zero_branch Q hQ hn 0 Fin.elim0 b
  rwa [batchedOuterPlan_round_run Q hQ]

theorem actualRoundSource_total (Q : Point) (hQ : order • Q=0) :
    (actualRoundSource Q).run.bornMass (ket zeroBasisState)=1 := by
  rw [← batchedOuterPlan_round_run Q hQ 0 Fin.elim0]
  exact AdaptiveCircuit.run_bornMass_eq_one _
    (Straight.instantiate_wellFormed _ _ _ (batchedOuterPlan_round_wellFormed 0)) _ (normSq_ket _)

theorem actualCompiledRepeat_retry_mass (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (count start : Nat) (history : Fin start → Bool) (accept : List Bool → Bool) :
    Instrument.bornMass
      ((((batchedOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run).filter
        (fun b => !repeatWindowFailed (actualRoundSource Q) accept count b.history)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass ((actualRoundSource Q).run.filter (fun b => accept b.history)) (ket zeroBasisState)) count := by
  rw [batchedOuterPlan_repeat_run Q hQ count start history]
  exact repeatWindowSuccess_mass _ accept (actualRoundSource_zero_branch Q hQ hn) (actualRoundSource_total Q hQ) count

theorem actualCompiledRepeat_zero_branch (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (count start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  rw [batchedOuterPlan_repeat_run Q hQ count start history] at hb
  exact repeatWindowProgram_zero _ (actualRoundSource_zero_branch Q hQ hn) count b hb
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_RoundReset

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.RepeatEvent -/
section Port_RepeatEvent

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] batchedOuterPlan actualRoundSource

theorem readWord_append_shift (before history : List Bool) (positions : List Nat) :
    readWord (before ++ history) (positions.map (before.length + ·)) = readWord history positions := by
  induction positions with
  | nil => rfl
  | cons i ps ih =>
    simp only [List.map_cons,readWord,List.getElem?_append_right (show before.length ≤ before.length+i by omega),Nat.add_sub_cancel_left,ih]

theorem readWord_suffix (history suffix : List Bool) (positions : List Nat)
    (h : ∀ i ∈ positions, i < history.length) :
    readWord (history ++ suffix) positions = readWord history positions := by
  induction positions with
  | nil => rfl
  | cons i ps ih =>
    simp only [readWord,List.getElem?_append_left (h i (by simp)),ih (fun j hj => h j (by simp [hj]))]

theorem axisPositions_shift {n : Nat} (ws : List (OuterWindow n)) (start offset : Nat) :
    axisPositions ws (offset+start) = (axisPositions ws start).map (offset+·) := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [axisPositions,List.map_append,Nat.add_assoc,ih]
    congr 1


def planRoundAccept {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (start : Nat) (history : List Bool) : Bool :=
  fixedPairAccept (axisPositions p.left.toList start)
    (axisPositions p.right.toList (start+axisCount p.left.toList)) accept history

theorem planRoundAccept_shift {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (start : Nat) (before history : List Bool) :
    planRoundAccept p accept (before.length+start) (before++history) =
      planRoundAccept p accept start history := by
  simp only [planRoundAccept,fixedPairAccept,Nat.add_assoc,
    axisPositions_shift,readWord_append_shift]

theorem planRoundAccept_suffix {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (history suffix : List Bool) (h : history.length = p.stride) :
    planRoundAccept p accept 0 (history++suffix) = planRoundAccept p accept 0 history := by
  have hl : ∀ i ∈ axisPositions p.left.toList 0, i < history.length := by
    intro i hi
    have := (axisPositions_bounds _ _ _ hi).2
    rw [h]; simp only [OuterPlan.stride]; omega
  have hr : ∀ i ∈ axisPositions p.right.toList (0+axisCount p.left.toList), i < history.length := by
    intro i hi
    have := (axisPositions_bounds _ _ _ hi).2
    rw [h]; simp only [OuterPlan.stride]; omega
  simp only [planRoundAccept,fixedPairAccept,readWord_suffix history suffix _ hl,
    readWord_suffix history suffix _ hr]

def planRepeatAccept {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (count : Nat) (history : List Bool) : Bool :=
  (List.range count).any (fun r => planRoundAccept p accept (r*p.stride) history)

theorem planRepeatAccept_cons {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (count : Nat) (before history : List Bool) (h : before.length=p.stride) :
    planRepeatAccept p accept (count+1) (before++history) =
      (planRoundAccept p accept 0 before || planRepeatAccept p accept count history) := by
  simp only [planRepeatAccept,List.range_succ_eq_map,List.any_cons,List.any_map,
    Nat.zero_mul,planRoundAccept_suffix p accept before history h]
  congr 1
  apply congrArg (List.any (List.range count))
  funext r
  dsimp only [Function.comp_def]
  rw [Nat.succ_mul,← h,Nat.add_comm,planRoundAccept_shift]

private theorem port_RepeatEvent_round_records_length {n : Nat} (p : OuterPlan n)
    (read : ConstantBit n → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.round 0).instantiate read Fin.elim0).run) :
    b.history.length = p.stride := by
  have h := straight_history_length _ read Fin.elim0 b hb
  simpa only [Nat.zero_add,Nat.sub_zero] using h

theorem actualRoundSource_records (Q : Point) (hQ : order • Q=0)
    (b : InstrumentBranch) (hb : b ∈ (actualRoundSource Q).run) :
    b.history.length = batchedOuterPlan.stride := by
  rw [← batchedOuterPlan_round_run Q hQ 0 Fin.elim0] at hb
  exact port_RepeatEvent_round_records_length _ _ b hb

theorem planRepeatAccept_retry (Q : Point) (hQ : order • Q=0)
    (accept : Nat → Nat → Bool) (count : Nat) (b : InstrumentBranch)
    (hb : b ∈ (repeatWindowProgram (actualRoundSource Q) count).run) :
    planRepeatAccept batchedOuterPlan accept count b.history =
      !repeatWindowFailed (actualRoundSource Q) (planRoundAccept batchedOuterPlan accept 0) count b.history := by
  induction count generalizing b with
  | zero => rfl
  | succ count ih =>
    rw [repeatWindowProgram,AdaptiveCircuit.run_seq] at hb
    obtain ⟨a,ha,hc⟩ := List.mem_flatMap.mp hb
    obtain ⟨c,hcRun,rfl⟩ := List.mem_map.mp hc
    rw [show (a.seq c).history = a.history++c.history from rfl,
      planRepeatAccept_cons _ _ count _ _ (actualRoundSource_records Q hQ a ha),ih c hcRun]
    simp only [repeatWindowFailed,consumeAdaptiveHistory_run _ a ha,
      List.length_append,Nat.add_sub_cancel_right,List.take_left,Bool.not_and,Bool.not_not]

private theorem port_RepeatEvent_find_isSome_any {α : Type} (p : α → Bool) (xs : List α) :
    (xs.find? p).isSome = xs.any p := by
  apply Bool.eq_iff_iff.mpr
  exact List.find?_isSome.trans List.any_eq_true.symm

theorem wrappedLayout_verified_any (params : DecoderParams) (Q : Point)
    (positions : List (TrialPositions params)) (h : positions.length ≤ 56) (history : List Bool) :
    (verifiedCandidate ⟨.wrappedShift,params,positions,h⟩ Q history).isSome =
      positions.any (fun pos => fixedPairAccept pos.left.toList pos.right.toList
        (wrappedPairAccept params Q) history) := by
  classical
  simp only [verifiedCandidate,candidates,port_RepeatEvent_find_isSome_any,List.any_flatMap]
  apply List.any_congr rfl
  intro pos
  have hh := wrappedTrial_verified_isSome params Q pos history
  simpa only [verifiedCandidate,candidates,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,port_RepeatEvent_find_isSome_any] using hh

theorem OuterPlan.verified_repeat_event {n : Nat} (p : OuterPlan n) (Q : Point) (history : List Bool) :
    (verifiedCandidate p.layoutForStreaming Q history).isSome =
      planRepeatAccept p (wrappedPairAccept legacyDecoderParams Q) streamingRounds history := by
  rw [OuterPlan.layoutForStreaming,wrappedLayout_verified_any]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,planRepeatAccept,List.mem_range]
  constructor
  · rintro ⟨pos,⟨r,rfl⟩,hr⟩
    exact ⟨r.val,r.isLt,by simpa only [OuterPlan.positionsForStreaming,Vector.toList,List.toList_toArray,planRoundAccept] using hr⟩
  · rintro ⟨r,hr,haccept⟩
    exact ⟨p.positionsForStreaming ⟨r,hr⟩,⟨⟨r,hr⟩,rfl⟩,by
      simpa only [OuterPlan.positionsForStreaming,Vector.toList,List.toList_toArray,planRoundAccept] using haccept⟩

private theorem port_RepeatEvent_roundAccept_zero {n : Nat} (p : OuterPlan n) (accept : Nat → Nat → Bool)
    (history : List Bool) :
    fixedPairAccept (p.positions ⟨0,by decide⟩).left.toList
      (p.positions ⟨0,by decide⟩).right.toList accept history = planRoundAccept p accept 0 history := by
  simp only [OuterPlan.positions,Vector.toList,List.toList_toArray,Nat.zero_mul,planRoundAccept]

theorem actualRoundFixedAccept_eq (accept : Nat → Nat → Bool) (history : List Bool) :
    actualRoundFixedAccept accept history = planRoundAccept batchedOuterPlan accept 0 history :=
  port_RepeatEvent_roundAccept_zero _ accept history

theorem actualCompiledRepeat_verified_event (Q : Point) (hQ : order • Q=0)
    (b : InstrumentBranch)
    (hb : b ∈ ((batchedOuterPlan.repeat streamingRounds 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run) :
    (verifiedCandidate batchedOuterPlan.layoutForStreaming Q b.history).isSome =
      !repeatWindowFailed (actualRoundSource Q)
        (actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q)) streamingRounds b.history := by
  rw [OuterPlan.verified_repeat_event]
  have hh := planRepeatAccept_retry Q hQ (wrappedPairAccept legacyDecoderParams Q) streamingRounds b
    (by rwa [batchedOuterPlan_repeat_run Q hQ] at hb)
  have he : actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) =
      planRoundAccept batchedOuterPlan (wrappedPairAccept legacyDecoderParams Q) 0 :=
    funext (actualRoundFixedAccept_eq _)
  rw [he]
  exact hh


/-- The protected final decoder tests exactly the independent retry event of the actual streamingRounds rounds. -/
theorem actualCompiledRepeat_verified_mass (Q : Point) (hQ : order • Q=0) (hn : Q≠0) :
    Instrument.bornMass
      ((((batchedOuterPlan.repeat streamingRounds 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate batchedOuterPlan.layoutForStreaming Q b.history).isSome)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass ((actualRoundSource Q).run.filter
          (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history)) (ket zeroBasisState)) streamingRounds := by
  have he := List.filter_congr (actualCompiledRepeat_verified_event Q hQ)
  rw [he]
  exact actualCompiledRepeat_retry_mass Q hQ hn streamingRounds 0 Fin.elim0 _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_RepeatEvent

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowBranchSum -/
section Port_WindowBranchSum

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes actualBatchedWindowState

/-- Physical Fourier coefficients retain the full previous measurement history. -/
theorem branchCoeff_amplitude (dir : PhaseDir) (ws : List Wire)
    (hws : ws.Nodup) (prior bs : List Bool) (s : BasisState) :
    fourierBranchCoeff dir ws prior bs s = fourierBitAmplitude dir (ws.map s) prior bs := by
  induction ws generalizing prior bs s with
  | nil => cases bs <;> rfl
  | cons w ws ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      simp only [fourierBranchCoeff, List.map_cons, fourierBitAmplitude]
      rw [ih hws.tail]
      have hm : ws.map (s[w ↦ false]) = ws.map s := by
        apply List.map_congr_left
        intro v hv
        have hvw : v ≠ w := by intro he; subst v; exact (List.nodup_cons.mp hws).1 hv
        simp [upd, hvw]
      rw [hm]

theorem window_branch_uniform (dir : PhaseDir) (ws : List Wire) (hn : ws.Nodup)
    (f : BasisState → BasisState) (prior output : List Bool)
    (s : BasisState) (hz : Clean ws s)
    (hf : ∀ input ∈ fourierOutcomes ws.length,
      ws.map (f (phaseWordState ws input s)) = input) :
    fourierBranch dir ws.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ f (Quantum.run (ws.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ ws.length) •
        ((fourierOutcomes ws.length).map (fun input =>
          fourierBitAmplitude dir input.reverse prior output •
            ket (fourierClear ws.reverse (f (phaseWordState ws input s))))).sum := by
  classical
  rw [phaseHadamards_uniform ws hn s hz, map_smul, map_smul]
  congr 1
  simp only [phaseUniformSum, map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [show Finsupp.lmapDomain ℂ ℂ f (ket (phaseWordState ws input s)) =
      ket (f (phaseWordState ws input s)) by simp [ket],
    fourierBranch_ket, branchCoeff_amplitude dir ws.reverse (List.nodup_reverse.mpr hn)]
  rw [List.map_reverse, hf input hi]

theorem phaseWordState_preserves (V : BasisState → Prop) (ws : List Wire)
    (hV : ∀ s, V s → ∀ w ∈ ws, ∀ b, V (s[w ↦ b]))
    (input : List Bool) (s : BasisState) (hs : V s) :
    V (phaseWordState ws input s) := by
  induction ws generalizing s input with
  | nil => exact hs
  | cons w ws ih =>
    cases input with
    | nil => exact hs
    | cons b input =>
      exact ih (fun t ht v hv c => hV t ht v (List.mem_cons_of_mem w hv) c)
        input _ (hV s hs w (by simp) b)

theorem actual_window_address_word (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    streamAddress.map (actualBatchedWindowState Q w (phaseWordState streamAddress input s)) = input := by
  have hv : BatchedWindowValid (phaseWordState streamAddress input s) :=
    phaseWordState_preserves BatchedWindowValid streamAddress
      (fun t ht v hv b => batchedWindowValid_address_update t ht v hv b) input s hs
  calc
    _ = streamAddress.map (phaseWordState streamAddress input s) := by
      apply List.map_congr_left
      intro v hva
      exact actualBatchedWindowState_frame Q hQ hn w _ hv v
        ((show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hva)
    _ = input := phaseWordState_word streamAddress (by decide +kernel) input hi s

/-- Exact amplitude sum for an actual corrected window and one fixed Fourier
output. All input amplitudes are added before any Born mass is taken. -/
theorem actual_window_branch_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (prior output : List Bool) (s : BasisState)
    (hs : BatchedWindowValid s) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (fourierClear streamAddress.reverse
              (actualBatchedWindowState Q w (phaseWordState streamAddress input s))))).sum := by
  simpa only [show streamAddress.length = 16 by decide +kernel] using
    window_branch_uniform .inverse streamAddress (by decide +kernel)
      (actualBatchedWindowState Q w) prior output s hz
      (fun input hi => actual_window_address_word Q hQ hn w s hs input
        ((fourierOutcomes_mem _ _).mp hi))

theorem actual_first_address_word (Q : Point) (s : BasisState)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    streamAddress.map (actualFirstWindowState Q (phaseWordState streamAddress input s)) = input := by
  calc
    _ = streamAddress.map (phaseWordState streamAddress input s) := by
      apply List.map_congr_left
      intro v hva
      have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hva
      simp only [actualFirstWindowState, pointWrite, if_neg hp]
    _ = input := phaseWordState_word streamAddress (by decide +kernel) input hi s

/-- The first direct-load window obeys the same amplitude-sum rule, including
infinity rows in its mixed table. -/
theorem actual_first_branch_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (fourierClear streamAddress.reverse
              (actualFirstWindowState Q (phaseWordState streamAddress input s))))).sum := by
  simpa only [show streamAddress.length = 16 by decide +kernel] using
    window_branch_uniform .inverse streamAddress (by decide +kernel)
      (actualFirstWindowState Q) prior output s hz
      (fun input hi => actual_first_address_word Q s input ((fourierOutcomes_mem _ _).mp hi))

theorem clear_assigned_point (ws : List Wire) (input : List Bool) (s : BasisState)
    (hz : Clean ws s) (hd : ∀ v ∈ ws, v ∉ pointLogicalWires) (P : Point) :
    fourierClear ws.reverse (pointWrite P (phaseWordState ws input s)) = pointWrite P s := by
  funext v
  rw [fourierClear_apply]
  by_cases hv : v ∈ ws
  · have hp := hd v hv
    simp only [List.mem_reverse, hv, if_true, pointWrite, if_neg hp]
    exact (hz v hv).symm
  · simp only [List.mem_reverse, hv, if_false, pointWrite]
    split
    · rfl
    · exact phaseWordState_frame ws input s v hv

theorem assigned_window_digit (input : List Bool) (hi : input.length = streamAddress.length)
    (s : BasisState) :
    windowRawDigit 0 (phaseWordState streamAddress input s) = boolWordToNat input := by
  have ha (t : BasisState) : tableAddressValue streamAddress t = windowRawDigit 0 t := by
    simp [streamAddress, tableAddressValue, windowRawDigit, windowAddressBits, windowBankStart,
      List.range', wireValues, boolWordToNat]
    omega
  rw [← ha]
  have word := phaseWordState_word streamAddress (by decide +kernel) input hi s
  change boolWordToNat (wireValues streamAddress (phaseWordState streamAddress input s)) = _
  rw [word]


theorem phaseWordState_pointWrite (ws : List Wire) (hd : ∀ w ∈ ws, w ∉ pointLogicalWires)
    (input : List Bool) (P : Point) (s : BasisState) :
    phaseWordState ws input (pointWrite P s) = pointWrite P (phaseWordState ws input s) := by
  induction ws generalizing input s with
  | nil => rfl
  | cons w ws ih =>
    cases input with
    | nil => rfl
    | cons b input =>
      have he : (pointWrite P s)[w ↦ b] = pointWrite P (s[w ↦ b]) := by
        funext v
        have hw := hd w (by simp)
        by_cases hv : v = w
        · subst v; simp [pointWrite, hw, upd]
        · by_cases hp : v ∈ pointLogicalWires <;> simp [pointWrite, hp, upd, hv]
      simp only [phaseWordState, he]
      exact ih (fun v hv => hd v (List.mem_cons_of_mem w hv)) input _

theorem assigned_point_coordinates (input : List Bool) (s : BasisState) (P : Point) :
    pointStateCoordinates (phaseWordState streamAddress input (pointWrite P s)) = fig14PointEncoding P := by
  rw [phaseWordState_pointWrite streamAddress (by decide +kernel), pointWrite_coordinates]

noncomputable def windowDigitPoint (Q : Point) : OddWindow → Nat → Point
  | .left j, digit => signedTableOdd 32768 digit •
      ((2 ^ (16 * j.val)) • signedWindowHalfPoint G order)
  | .right j, digit => signedTableOdd 32768 digit •
      ((2 ^ (16 * j.val)) • signedWindowHalfPoint Q order)

theorem actual_window_digit (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite (P + windowDigitPoint Q w (windowRawDigit 0 s)) s := by
  cases w with
  | left j => exact actual_left_window_digit Q hQ hn j s hs P hP
  | right j => exact actual_right_window_digit Q hQ hn j s hs P hP

theorem actual_window_assigned_clear (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (P : Point) (s : BasisState) (hs : FirstWindowInput s)
    (hz : Clean streamAddress s) (input : List Bool) (hi : input.length = streamAddress.length) :
    fourierClear streamAddress.reverse
      (actualBatchedWindowState Q w (phaseWordState streamAddress input (pointWrite P s))) =
      pointWrite (P + windowDigitPoint Q w (boolWordToNat input)) s := by
  have hv : BatchedWindowValid (phaseWordState streamAddress input (pointWrite P s)) :=
    phaseWordState_preserves BatchedWindowValid streamAddress
      (fun t ht v hv b => batchedWindowValid_address_update t ht v hv b)
      input _ (firstWindowInput_pointWrite s hs P)
  have hc : Clean streamAddress (pointWrite P s) := by
    intro v hv
    have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hv
    simpa only [pointWrite, if_neg hp] using hz v hv
  rw [actual_window_digit Q hQ hn w _ hv.1 P (assigned_point_coordinates input s P),
    assigned_window_digit input hi,
    clear_assigned_point streamAddress input (pointWrite P s) hc (by decide +kernel)]
  funext v
  simp only [pointWrite]
  split <;> rfl

theorem actual_first_assigned_clear (Q : Point) (s : BasisState) (hz : Clean streamAddress s)
    (input : List Bool) (hi : input.length = streamAddress.length) :
    fourierClear streamAddress.reverse (actualFirstWindowState Q (phaseWordState streamAddress input s)) =
      pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
        signedTableOdd 32768 (boolWordToNat input) •
          ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s := by
  rw [actual_first_window_digit, assigned_window_digit input hi,
    clear_assigned_point streamAddress input s hz (by decide +kernel)]

theorem actual_window_point_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (prior output : List Bool) (P : Point) (s : BasisState)
    (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)
        (Quantum.run (streamAddress.map Gate.H) (ket (pointWrite P s)))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (P + windowDigitPoint Q w (boolWordToNat input)) s))).sum := by
  have hc : Clean streamAddress (pointWrite P s) := by
    intro v hv
    have hp := (show ∀ v ∈ streamAddress, v ∉ pointLogicalWires by decide +kernel) v hv
    simpa only [pointWrite, if_neg hp] using hz v hv
  rw [actual_window_branch_sum Q hQ hn w prior output _
    (firstWindowInput_pointWrite s hs P) hc]
  apply congrArg (fun φ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • φ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [actual_window_assigned_clear Q hQ hn w P s hs hz input
    (by simpa only [show streamAddress.length = 16 by decide +kernel] using (fourierOutcomes_mem 16 input).mp hi)]

theorem actual_first_point_sum (Q : Point) (prior output : List Bool)
    (s : BasisState) (hz : Clean streamAddress s) :
    fourierBranch .inverse streamAddress.reverse prior output
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
        (Quantum.run (streamAddress.map Gate.H) (ket s))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            ket (pointWrite (axisWindowOffset G 16 + axisWindowOffset Q 13 +
              signedTableOdd 32768 (boolWordToNat input) •
                ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)) s))).sum := by
  rw [actual_first_branch_sum Q prior output s hz]
  apply congrArg (fun φ : State => (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) • φ)
  apply congrArg List.sum
  apply List.map_congr_left
  intro input hi
  rw [actual_first_assigned_clear Q s hz input
    (by simpa only [show streamAddress.length = 16 by decide +kernel] using (fourierOutcomes_mem 16 input).mp hi)]

/-- Fixed Fourier outputs for an axis, before the terminal event is selected. -/
noncomputable def actualAxisBranch (Q : Point) :
    List (OddWindow × List Bool) → List Bool → State →ₗ[ℂ] State
  | [], _ => LinearMap.id
  | (w, output) :: windows, prior =>
      (actualAxisBranch Q windows (output.reverse ++ prior)).comp
        ((fourierBranch .inverse streamAddress.reverse prior output).comp
          ((Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)).comp
            (Quantum.run (streamAddress.map Gate.H))))

/-- The exact coherent point-state sum, retaining interference between inputs. -/
noncomputable def pointAxisKernel (Q : Point) (s : BasisState) :
    List (OddWindow × List Bool) → List Bool → Point → State
  | [], _, P => ket (pointWrite P s)
  | (w, output) :: windows, prior, P =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun input =>
          fourierBitAmplitude .inverse input.reverse prior output •
            pointAxisKernel Q s windows (output.reverse ++ prior)
              (P + windowDigitPoint Q w (boolWordToNat input)))).sum

/-- Induction over the actual windows reduces execution to a coherent point sum;
there is no classical mixture over inputs and no exceptional-event loss. -/
theorem actualAxisBranch_point (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s)
    (windows : List (OddWindow × List Bool)) (prior : List Bool) (P : Point) :
    actualAxisBranch Q windows prior (ket (pointWrite P s)) =
      pointAxisKernel Q s windows prior P := by
  induction windows generalizing prior P with
  | nil => rfl
  | cons w windows ih =>
    simp only [actualAxisBranch, LinearMap.comp_apply]
    rw [actual_window_point_sum Q hQ hn w.1 prior w.2 P s hs hz]
    simp only [map_smul, map_list_sum, List.map_map, Function.comp_def, ih, pointAxisKernel]

noncomputable def windowOutputPaths : List OddWindow → List (List (OddWindow × List Bool))
  | [] => [[]]
  | w :: windows => (fourierOutcomes 16).flatMap (fun bits =>
      (windowOutputPaths windows).map (fun path => (w, bits) :: path))

theorem selectedIdealAxis_paths (Q : Point) (windows : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) :
    selectedIdealAxis Q windows prior terminal =
      (windowOutputPaths windows).flatMap (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).map (fun b =>
          InstrumentBranch.seq ⟨(path.map Prod.snd).flatten, actualAxisBranch Q path prior⟩ b)) := by
  induction windows generalizing prior with
  | nil =>
    simp only [selectedIdealAxis, windowOutputPaths, List.flatMap_cons, List.flatMap_nil,
      List.map_nil, List.flatten_nil, List.reverse_nil, List.nil_append, List.append_nil,
      actualAxisBranch]
    apply Eq.symm
    exact List.map_id' _
  | cons w windows ih =>
    simp only [selectedIdealAxis, fourierContinuationInstrument, ih, windowOutputPaths,
      List.map_flatMap, List.flatMap_map, List.flatMap_assoc, List.map_map,
      Function.comp_def, List.map_cons, List.flatten_cons, List.reverse_append,
      List.append_assoc, actualAxisBranch]
    apply List.flatMap_congr
    intro output ho
    apply List.flatMap_congr
    intro path hp
    apply List.map_congr_left
    intro b hb
    cases b
    simp [InstrumentBranch.seq, LinearMap.comp_assoc, List.append_assoc]

theorem selectedIdealAxis_paths_mass (Q : Point) (windows : List OddWindow)
    (prior : List Bool) (terminal : List Bool → Instrument) (ψ : State) :
    (selectedIdealAxis Q windows prior terminal).bornMass ψ =
      ((windowOutputPaths windows).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (actualAxisBranch Q path prior ψ))).sum := by
  rw [selectedIdealAxis_paths]
  simp only [Instrument.bornMass, List.map_flatMap, List.map_map,
    Function.comp_def, InstrumentBranch.seq, LinearMap.comp_apply]
  generalize windowOutputPaths windows = paths
  induction paths with
  | nil => rfl
  | cons path paths ih =>
    simpa only [List.flatMap_cons, List.map_cons, List.sum_cons, List.sum_append] using
      congrArg (_ + ·) ih

theorem selectedIdealAxis_point_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (windows : List OddWindow) (prior : List Bool) (terminal : List Bool → Instrument)
    (P : Point) (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealAxis Q windows prior terminal).bornMass (ket (pointWrite P s)) =
      ((windowOutputPaths windows).map (fun path =>
        (terminal ((path.map Prod.snd).flatten.reverse ++ prior)).bornMass
          (pointAxisKernel Q s path prior P))).sum := by
  rw [selectedIdealAxis_paths_mass]
  simp only [actualAxisBranch_point Q hQ hn s hs hz]

end
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WindowBranchSum

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.IdealDistribution -/
section Port_IdealDistribution

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum Secp256k1
noncomputable section
attribute [local irreducible] fourierOutcomes

def axisInputWords : Nat → List (List (List Bool))
  | 0 => [[]]
  | n+1 => (fourierOutcomes 16).flatMap (fun input =>
      (axisInputWords n).map (fun rest => input :: rest))

def axisInputEnd (Q : Point) : List (OddWindow × List Bool) → List (List Bool) → Point → Point
  | (w, _) :: windows, input :: inputs, P =>
      axisInputEnd Q windows inputs (P + windowDigitPoint Q w (boolWordToNat input))
  | _, _, P => P

def axisInputWeight : List (OddWindow × List Bool) → List Bool → List (List Bool) → ℂ
  | (_, output) :: windows, prior, input :: inputs =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) *
        fourierBitAmplitude .inverse input.reverse prior output *
          axisInputWeight windows (output.reverse ++ prior) inputs
  | _, _, _ => 1

private theorem port_IdealDistribution_flat_sum {A B : Type} [AddCommMonoid B] (xs : List A) (f : A → List B) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

theorem pointAxisKernel_inputs (Q : Point) (s : BasisState)
    (windows : List (OddWindow × List Bool)) (prior : List Bool) (P : Point) :
    pointAxisKernel Q s windows prior P =
      ((axisInputWords windows.length).map (fun inputs =>
        axisInputWeight windows prior inputs • ket (pointWrite (axisInputEnd Q windows inputs P) s))).sum := by
  induction windows generalizing prior P with
  | nil => simp [pointAxisKernel, axisInputWords, axisInputWeight, axisInputEnd]
  | cons w windows ih =>
    simp only [pointAxisKernel, List.length_cons, axisInputWords, List.map_flatMap,
      List.map_map, Function.comp_def, axisInputWeight, axisInputEnd, port_IdealDistribution_flat_sum]
    simp_rw [ih]
    simp only [smul_smul, List.smul_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro input hi
    congr 1
    apply List.map_congr_left
    intro inputs his
    rw [mul_assoc]
def axisInputPairs (windows : List (OddWindow × List Bool)) (inputs : List (List Bool)) :
    List (List Bool × List Bool) :=
  (windows.zip inputs).map (fun p => (p.2.reverse, p.1.2))

theorem axisInputWeight_amplitude (windows : List (OddWindow × List Bool))
    (prior : List Bool) (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    axisInputWeight windows prior inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (16 * windows.length)) *
        windowFourierAmplitude .inverse (axisInputPairs windows inputs) prior := by
  induction windows generalizing prior inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [axisInputWeight, axisInputPairs, windowFourierAmplitude]
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = windows.length := by simpa using hl
      simp only [axisInputWeight, axisInputPairs, List.zip_cons_cons, List.map_cons,
        windowFourierAmplitude, List.length_cons]
      rw [ih _ inputs ht]
      change _ = _ * (fourierBitAmplitude .inverse input.reverse prior w.2 *
        windowFourierAmplitude .inverse (axisInputPairs windows inputs) (w.2.reverse ++ prior))
      rw [show 16 * (windows.length + 1) = 16 + 16 * windows.length by omega, pow_add]
      ring

theorem axisInputPairs_lengths (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool))
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    ∀ pair ∈ axisInputPairs windows inputs, pair.2.length = pair.1.length := by
  intro pair hp
  unfold axisInputPairs at hp
  obtain ⟨p, hzip, he⟩ := List.mem_map.mp hp
  subst pair
  have hw := List.of_mem_zip hzip
  simp only [List.length_reverse]
  rw [ho p.1 hw.1, hi p.2 hw.2]

/-- The coefficient of a whole input path has the exact full-axis kernel,
including both Hadamard preparation and Fourier normalization. -/
theorem axisInputWeight_kernel (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length)
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    axisInputWeight windows List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (16 * windows.length)) *
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ ((axisInputPairs windows inputs).map Prod.fst).flatten.length) *
        dyadicFourierKernel .inverse ((axisInputPairs windows inputs).map Prod.fst).flatten.length
          (fourierWordMSB ((axisInputPairs windows inputs).map Prod.fst).flatten)
          (fourierWordLSB ((axisInputPairs windows inputs).map Prod.snd).flatten) := by
  rw [axisInputWeight_amplitude windows List.nil inputs hl,
    windowFourierAmplitude_kernel .inverse _ (axisInputPairs_lengths windows inputs ho hi)]
  ring

theorem fourierOutcomes_reverse_perm (n : Nat) :
    ((fourierOutcomes n).map List.reverse).Perm (fourierOutcomes n) := by
  apply (List.perm_ext_iff_of_nodup
    ((fourierOutcomes_nodup n).map List.reverse_injective) (fourierOutcomes_nodup n)).mpr
  intro bits
  simp only [List.mem_map, fourierOutcomes_mem]
  constructor
  · rintro ⟨xs, hx, rfl⟩
    simpa only [List.length_reverse] using hx
  · intro hb
    exact ⟨bits.reverse, by simpa using hb, List.reverse_reverse bits⟩

theorem fourierOutcomes_append (n m : Nat) : fourierOutcomes (n + m) =
    (fourierOutcomes n).flatMap (fun a => (fourierOutcomes m).map (fun b => a ++ b)) := by
  induction n with
  | zero => simp [fourierOutcomes]
  | succ n ih =>
    simp only [Nat.succ_add, fourierOutcomes, ih, List.flatMap_append, List.flatMap_map,
      List.map_flatMap, List.map_map, Function.comp_def, List.cons_append]

theorem axisInputWords_flatten (n : Nat) :
    (axisInputWords n).map List.flatten = fourierOutcomes (16 * n) := by
  induction n with
  | zero => simp [axisInputWords, fourierOutcomes]
  | succ n ih =>
    rw [show 16 * (n + 1) = 16 + 16 * n by omega, fourierOutcomes_append]
    simp only [axisInputWords, List.map_flatMap, List.map_map, Function.comp_def, List.flatten_cons]
    apply congrArg (List.flatMap · (fourierOutcomes 16))
    funext input
    simpa only [List.map_map, Function.comp_def] using congrArg (List.map (input ++ ·)) ih

theorem axisInputWords_mem (n : Nat) (inputs : List (List Bool)) :
    inputs ∈ axisInputWords n ↔ inputs.length = n ∧ ∀ bits ∈ inputs, bits.length = 16 := by
  induction n generalizing inputs with
  | zero => cases inputs <;> simp [axisInputWords]
  | succ n ih =>
    cases inputs with
    | nil => simp [axisInputWords, List.mem_flatMap]
    | cons input inputs =>
      simp [axisInputWords, List.mem_flatMap, List.mem_map, List.cons.injEq,
        fourierOutcomes_mem, ih, and_assoc, and_left_comm, and_comm]

theorem axisInputWords_reverse_perm (n : Nat) :
    ((axisInputWords n).map (List.map List.reverse)).Perm (axisInputWords n) := by
  induction n with
  | zero => simp [axisInputWords]
  | succ n ih =>
    simp only [axisInputWords]
    have he : ((fourierOutcomes 16).flatMap (fun input =>
        (axisInputWords n).map (fun rest => input :: rest))).map (List.map List.reverse) =
      ((fourierOutcomes 16).map List.reverse).flatMap (fun input =>
        ((axisInputWords n).map (List.map List.reverse)).map (fun rest => input :: rest)) := by
      simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, List.map_cons]
    rw [he]
    exact (fourierOutcomes_reverse_perm 16).flatMap (fun input _ => ih.map (input :: ·))

/-- Reversing each physical input window gives every full MSB-first input word
exactly once, so regrouping the coherent sum does not change multiplicity. -/
theorem axisInputWords_msb_perm (n : Nat) :
    ((axisInputWords n).map (fun inputs => (inputs.map List.reverse).flatten)).Perm
      (fourierOutcomes (16 * n)) := by
  have hp := (axisInputWords_reverse_perm n).map List.flatten
  simpa only [List.map_map, Function.comp_def, axisInputWords_flatten] using hp

theorem axisInputEnd_sum (Q : Point) (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (P : Point) :
    axisInputEnd Q windows inputs P = P +
      ((windows.zip inputs).map (fun p => windowDigitPoint Q p.1.1 (boolWordToNat p.2))).sum := by
  induction windows generalizing inputs P with
  | nil => simp [axisInputEnd]
  | cons w windows ih =>
    cases inputs with
    | nil => simp [axisInputEnd]
    | cons input inputs =>
      simp only [axisInputEnd, List.zip_cons_cons, List.map_cons, List.sum_cons, ih]
      exact add_assoc _ _ _

theorem axisInputPairs_fst (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    (axisInputPairs windows inputs).map Prod.fst = inputs.map List.reverse := by
  induction windows generalizing inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [axisInputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

theorem axisInputPairs_snd (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length) :
    (axisInputPairs windows inputs).map Prod.snd = windows.map Prod.snd := by
  induction windows generalizing inputs with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs; rfl
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      simp only [axisInputPairs, List.zip_cons_cons, List.map_cons]
      congr 1
      exact ih inputs (by simpa using hl)

/-- A path has one preparation factor and one Fourier factor per input bit. -/
theorem axisInputWeight_full_kernel (windows : List (OddWindow × List Bool))
    (inputs : List (List Bool)) (hl : inputs.length = windows.length)
    (ho : ∀ w ∈ windows, w.2.length = 16) (hi : ∀ input ∈ inputs, input.length = 16) :
    axisInputWeight windows List.nil inputs =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ (32 * windows.length)) *
        dyadicFourierKernel .inverse (16 * windows.length)
          (fourierWordMSB (inputs.map List.reverse).flatten)
          (fourierWordLSB (windows.map Prod.snd).flatten) := by
  have hlen : (inputs.map List.reverse).flatten.length = 16 * windows.length := by
    rw [fixed_windows_flatten_length 16 _]
    · simp only [List.length_map, hl]
    · intro bits hb
      obtain ⟨input, hm, he⟩ := List.mem_map.mp hb
      subst bits
      simpa only [List.length_reverse] using hi input hm
  rw [axisInputWeight_kernel windows inputs hl ho hi,
    axisInputPairs_fst windows inputs hl, axisInputPairs_snd windows inputs hl, hlen,
    ← pow_add, show 16 * windows.length + 16 * windows.length = 32 * windows.length by omega]

def descendingOddValue : List Nat → Int
  | [] => 0
  | d :: ds => signedTableOdd 32768 d * 65536 ^ ds.length + descendingOddValue ds

private theorem port_IdealDistribution_signedValue_append (xs ys : List Int) :
    signedWindowValue 65536 (xs ++ ys) =
      signedWindowValue 65536 xs + (65536 : Int) ^ xs.length * signedWindowValue 65536 ys := by
  induction xs with
  | nil => simp [signedWindowValue]
  | cons x xs ih =>
    simp only [List.cons_append, signedWindowValue, List.length_cons, ih, pow_succ]
    ring

theorem descendingOddValue_reverse (digits : List Nat) :
    descendingOddValue digits = signedWindowValue 65536 (digits.reverse.map (signedTableOdd 32768)) := by
  induction digits with
  | nil => rfl
  | cons d ds ih =>
    simp only [descendingOddValue, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, port_IdealDistribution_signedValue_append, List.length_map, List.length_reverse,
      signedWindowValue, ih]
    ring

/-- Each chronological window uses the descending power belonging to its
remaining suffix. This proposition concerns only fixed labels and weights. -/
def DescendingAxisWeights (Q P : Point) : List (OddWindow × List Bool) → Prop
  | [] => True
  | (w, _) :: windows =>
      (∀ digit, windowDigitPoint Q w digit =
        signedTableOdd 32768 digit • (65536 ^ windows.length • signedWindowHalfPoint P order)) ∧
      DescendingAxisWeights Q P windows

theorem axisInputEnd_weighted (Q P : Point) (windows : List (OddWindow × List Bool))
    (hw : DescendingAxisWeights Q P windows) (inputs : List (List Bool))
    (hl : inputs.length = windows.length) (A : Point) :
    axisInputEnd Q windows inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint P order := by
  induction windows generalizing inputs A with
  | nil =>
    have he : inputs = [] := List.length_eq_zero_iff.mp hl
    subst inputs
    simp [axisInputEnd, descendingOddValue]
  | cons w windows ih =>
    cases inputs with
    | nil => simp at hl
    | cons input inputs =>
      have ht : inputs.length = windows.length := by simpa using hl
      simp only [axisInputEnd]
      rw [ih hw.2 inputs ht, hw.1]
      simp only [List.map_cons, descendingOddValue, List.length_map, ht, add_zsmul]
      rw [mul_zsmul, show (65536 : Int) ^ windows.length = ((65536 ^ windows.length : Nat) : Int) by norm_cast, natCast_zsmul]
      exact add_assoc _ _ _

def DescendingLabelWeights (Q P : Point) : List OddWindow → Prop
  | [] => True
  | w :: windows =>
      (∀ digit, windowDigitPoint Q w digit =
        signedTableOdd 32768 digit • (65536 ^ windows.length • signedWindowHalfPoint P order)) ∧
      DescendingLabelWeights Q P windows

theorem descendingLabelWeights_zip (Q P : Point) (windows : List OddWindow)
    (hw : DescendingLabelWeights Q P windows) (outputs : List (List Bool))
    (hl : outputs.length = windows.length) : DescendingAxisWeights Q P (windows.zip outputs) := by
  induction windows generalizing outputs with
  | nil => simp [DescendingAxisWeights]
  | cons w windows ih =>
    cases outputs with
    | nil => simp at hl
    | cons output outputs =>
      have ht : outputs.length = windows.length := by simpa using hl
      simp only [List.zip_cons_cons, DescendingAxisWeights, List.length_zip, ht, min_self]
      exact ⟨hw.1, ih hw.2 outputs ht⟩

theorem left_labels_weights (Q : Point) : DescendingLabelWeights Q G leftOddIndices := by
  norm_num [leftOddIndices, List.ofFn_succ, DescendingLabelWeights, windowDigitPoint, pow_mul]

theorem right_labels_weights (Q : Point) : DescendingLabelWeights Q Q rightOddIndices := by
  norm_num [rightOddIndices, List.ofFn_succ, DescendingLabelWeights, windowDigitPoint, pow_mul]

theorem left_axis_input_end (Q : Point) (outputs inputs : List (List Bool))
    (ho : outputs.length = 15) (hi : inputs.length = 15) (A : Point) :
    axisInputEnd Q (leftOddIndices.zip outputs) inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint G order := by
  apply axisInputEnd_weighted
  · apply descendingLabelWeights_zip Q G _ (left_labels_weights Q) outputs
    simpa only [leftOddIndices, List.length_ofFn] using ho
  · simpa only [List.length_zip, leftOddIndices, List.length_ofFn, ho, min_self] using hi

theorem right_axis_input_end (Q : Point) (outputs inputs : List (List Bool))
    (ho : outputs.length = 13) (hi : inputs.length = 13) (A : Point) :
    axisInputEnd Q (rightOddIndices.zip outputs) inputs A =
      A + descendingOddValue (inputs.map boolWordToNat) • signedWindowHalfPoint Q order := by
  apply axisInputEnd_weighted
  · apply descendingLabelWeights_zip Q Q _ (right_labels_weights Q) outputs
    simpa only [rightOddIndices, List.length_ofFn] using ho
  · simpa only [List.length_zip, rightOddIndices, List.length_ofFn, ho, min_self] using hi

theorem actual_two_axes_input_end (Q : Point) (hQ : order • Q = 0)
    (first : List Bool) (left right outputsL outputsR : List (List Bool))
    (hl : left.length = 15) (hr : right.length = 13)
    (hol : outputsL.length = 15) (hor : outputsR.length = 13) :
    axisInputEnd Q (rightOddIndices.zip outputsR) right
      (axisInputEnd Q (leftOddIndices.zip outputsL) left
        (axisWindowOffset G 16 + axisWindowOffset Q 13 +
          signedTableOdd 32768 (boolWordToNat first) •
            ((2 ^ (16 * 15)) • signedWindowHalfPoint G order))) =
      windowValue 65536 ((first :: left).map boolWordToNat).reverse • G +
        windowValue 65536 (right.map boolWordToNat).reverse • Q := by
  rw [right_axis_input_end Q outputsR right hor hr,
    left_axis_input_end Q outputsL left hol hl]
  have hgroup := two_axis_signed_digits Q hQ
    ((first :: left).map boolWordToNat).reverse (right.map boolWordToNat).reverse
    (by simp only [List.length_reverse, List.length_map, List.length_cons, hl])
    (by simp only [List.length_reverse, List.length_map, hr])
  rw [← descendingOddValue_reverse, ← descendingOddValue_reverse] at hgroup
  rw [← hgroup]
  simp only [List.map_cons, descendingOddValue, List.length_map, hl, add_zsmul, mul_zsmul]
  rw [show (65536 : Int) ^ 15 = ((65536 ^ 15 : Nat) : Int) by norm_cast, natCast_zsmul,
    show 2 ^ (16 * 15) = 65536 ^ 15 by decide +kernel]
  abel

/-- The actual two-axis branch is one coherent sum over all three input
blocks: the direct first load, the remaining left windows, and the right axis. -/
theorem actual_two_axes_state_sum (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (firstOutput : List Bool) (left right : List (OddWindow × List Bool))
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    actualAxisBranch Q right List.nil
      (actualAxisBranch Q left firstOutput.reverse
        (fourierBranch .inverse streamAddress.reverse List.nil firstOutput
          (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
            (Quantum.run (streamAddress.map Gate.H) (ket s))))) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 16) •
        ((fourierOutcomes 16).map (fun firstInput =>
          fourierBitAmplitude .inverse firstInput.reverse List.nil firstOutput •
            ((axisInputWords left.length).map (fun inputsL =>
              axisInputWeight left firstOutput.reverse inputsL •
                ((axisInputWords right.length).map (fun inputsR =>
                  axisInputWeight right List.nil inputsR •
                    ket (pointWrite
                      (axisInputEnd Q right inputsR
                        (axisInputEnd Q left inputsL
                          (axisWindowOffset G 16 + axisWindowOffset Q 13 +
                            signedTableOdd 32768 (boolWordToNat firstInput) •
                              ((2 ^ (16 * 15)) • signedWindowHalfPoint G order)))) s))).sum)).sum)).sum := by
  rw [actual_first_point_sum Q List.nil firstOutput s hz]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def,
    actualAxisBranch_point Q hQ hn s hs hz]
  simp_rw [pointAxisKernel_inputs]
  simp only [map_smul, map_list_sum, List.map_map, Function.comp_def,
    actualAxisBranch_point Q hQ hn s hs hz, pointAxisKernel_inputs]

def inputScalarWord (inputs : List (List Bool)) : List Bool :=
  (inputs.map List.reverse).flatten.reverse

theorem inputScalarWord_perm (n : Nat) :
    ((axisInputWords n).map inputScalarWord).Perm (fourierOutcomes (16 * n)) := by
  have hp := (axisInputWords_msb_perm n).map List.reverse
  simpa only [List.map_map, Function.comp_def, inputScalarWord] using
    hp.trans (fourierOutcomes_reverse_perm (16 * n))

theorem inputScalarWord_value (inputs : List (List Bool))
    (hi : ∀ bits ∈ inputs, bits.length = 16) :
    boolWordToNat (inputScalarWord inputs) =
      windowValue 65536 (inputs.map boolWordToNat).reverse := by
  rw [← fourierWordMSB_reverse]
  simp only [inputScalarWord, List.reverse_reverse]
  have h := input_windows_value 16 (inputs.map List.reverse) (by
    intro bits hb
    obtain ⟨input, hm, he⟩ := List.mem_map.mp hb
    subst bits
    simpa only [List.length_reverse] using hi input hm)
  simpa only [List.map_map, Function.comp_def, fourierWordMSB_reverse] using h

theorem two_axis_input_kernel (left right : List (OddWindow × List Bool))
    (inputsL inputsR : List (List Bool)) (hl : left.length = 16) (hr : right.length = 13)
    (hil : inputsL.length = left.length) (hir : inputsR.length = right.length)
    (hol : ∀ w ∈ left, w.2.length = 16) (hor : ∀ w ∈ right, w.2.length = 16)
    (hbl : ∀ bits ∈ inputsL, bits.length = 16) (hbr : ∀ bits ∈ inputsR, bits.length = 16) :
    axisInputWeight left List.nil inputsL * axisInputWeight right List.nil inputsR =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928) *
        dyadicFourierKernel .inverse 256 (boolWordToNat (inputScalarWord inputsL))
          (fourierWordLSB (left.map Prod.snd).flatten) *
        dyadicFourierKernel .inverse 208 (boolWordToNat (inputScalarWord inputsR))
          (fourierWordLSB (right.map Prod.snd).flatten) := by
  rw [axisInputWeight_full_kernel left inputsL hil hol hbl,
    axisInputWeight_full_kernel right inputsR hir hor hbr, hl, hr]
  have hw (inputs : List (List Bool)) :
      fourierWordMSB (inputs.map List.reverse).flatten = boolWordToNat (inputScalarWord inputs) := by
    simpa only [inputScalarWord, List.reverse_reverse] using
      fourierWordMSB_reverse (inputScalarWord inputs)
  rw [hw, hw, show (928 : Nat) = 32 * 16 + 32 * 13 by decide, pow_add]
  ring

theorem axisInputWords_sum_succ {A : Type} [AddCommMonoid A] (n : Nat)
    (f : List (List Bool) → A) :
    ((axisInputWords (n + 1)).map f).sum =
      ((fourierOutcomes 16).map (fun input =>
        ((axisInputWords n).map (fun inputs => f (input :: inputs))).sum)).sum := by
  simp only [axisInputWords, List.map_flatMap, List.map_map, Function.comp_def, port_IdealDistribution_flat_sum]

def twoAxisInputState (Q : Point) (s : BasisState) (x y : List Bool) : State :=
  ((axisInputWords 16).map (fun inputsL =>
    ((axisInputWords 13).map (fun inputsR =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
        dyadicFourierKernel .inverse 256 (boolWordToNat (inputScalarWord inputsL)) (fourierWordLSB x) *
        dyadicFourierKernel .inverse 208 (boolWordToNat (inputScalarWord inputsR)) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat (inputScalarWord inputsL) • G +
        boolWordToNat (inputScalarWord inputsR) • Q) s))).sum)).sum

theorem actual_two_axes_input_state (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (firstOutput : List Bool) (outputsL outputsR : List (List Bool))
    (ho0 : firstOutput.length = 16) (hol : outputsL.length = 15) (hor : outputsR.length = 13)
    (hbl : ∀ bits ∈ outputsL, bits.length = 16) (hbr : ∀ bits ∈ outputsR, bits.length = 16)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    actualAxisBranch Q (rightOddIndices.zip outputsR) List.nil
      (actualAxisBranch Q (leftOddIndices.zip outputsL) firstOutput.reverse
        (fourierBranch .inverse streamAddress.reverse List.nil firstOutput
          (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
            (Quantum.run (streamAddress.map Gate.H) (ket s))))) =
      twoAxisInputState Q s (firstOutput :: outputsL).flatten outputsR.flatten := by
  have hll : (leftOddIndices.zip outputsL).length = 15 := by
    simp only [List.length_zip, leftOddIndices, List.length_ofFn, hol, min_self]
  have hrl : (rightOddIndices.zip outputsR).length = 13 := by
    simp only [List.length_zip, rightOddIndices, List.length_ofFn, hor, min_self]
  rw [actual_two_axes_state_sum Q hQ hn firstOutput _ _ s hs hz, hll, hrl,
    twoAxisInputState, axisInputWords_sum_succ 15]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro firstInput hf
  apply congrArg List.sum
  apply List.map_congr_left
  intro inputsL hlm
  apply congrArg List.sum
  apply List.map_congr_left
  intro inputsR hrm
  have hf' := (fourierOutcomes_mem 16 firstInput).mp hf
  have hl' := (axisInputWords_mem 15 inputsL).mp hlm
  have hr' := (axisInputWords_mem 13 inputsR).mp hrm
  have hli : ∀ bits ∈ firstInput :: inputsL, bits.length = 16 := by
    intro bits hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hf'
    · exact hl'.2 bits hb
  rw [actual_two_axes_input_end Q hQ firstInput inputsL inputsR outputsL outputsR
    hl'.1 hr'.1 hol hor,
    ← inputScalarWord_value (firstInput :: inputsL) hli,
    ← inputScalarWord_value inputsR hr'.2]
  apply congrArg (fun c : ℂ => c • ket (pointWrite
    (boolWordToNat (inputScalarWord (firstInput :: inputsL)) • G +
      boolWordToNat (inputScalarWord inputsR) • Q) s))
  let left : List (OddWindow × List Bool) := (.left ⟨0, by decide⟩, firstOutput) :: leftOddIndices.zip outputsL
  have hcoef := two_axis_input_kernel left (rightOddIndices.zip outputsR)
    (firstInput :: inputsL) inputsR (by simp only [left, List.length_cons, hll]) hrl
    (by simp only [left, List.length_cons, hll, hl'.1]) (hr'.1.trans hrl.symm)
    (by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ho0
      · exact hbl w.2 (List.of_mem_zip hw).2)
    (fun w hw => hbr w.2 (List.of_mem_zip hw).2) hli hr'.2
  have hls : (leftOddIndices.zip outputsL).map Prod.snd = outputsL :=
    List.map_snd_zip (by simp only [leftOddIndices, List.length_ofFn, hol, le_refl])
  have hrs : (rightOddIndices.zip outputsR).map Prod.snd = outputsR :=
    List.map_snd_zip (by simp only [rightOddIndices, List.length_ofFn, hor, le_refl])
  simpa only [left, axisInputWeight, List.map_cons, hls, hrs, List.nil_append, List.append_nil,
    mul_assoc] using hcoef

theorem inputScalarWord_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((axisInputWords n).map (fun inputs => f (inputScalarWord inputs))).sum =
      ((fourierOutcomes (16 * n)).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using ((inputScalarWord_perm n).map f).sum_eq

def idealPointState (Q : Point) (s : BasisState) (x y : List Bool) : State :=
  ((fourierOutcomes 256).map (fun a =>
    ((fourierOutcomes 208).map (fun b =>
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
        dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x) *
        dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) s))).sum)).sum

theorem twoAxisInputState_ideal (Q : Point) (s : BasisState) (x y : List Bool) :
    twoAxisInputState Q s x y = idealPointState Q s x y := by
  let f (a b : List Bool) : State :=
    (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) ^ 928 *
      dyadicFourierKernel .inverse 256 (boolWordToNat a) (fourierWordLSB x) *
      dyadicFourierKernel .inverse 208 (boolWordToNat b) (fourierWordLSB y)) •
      ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q) s)
  change ((axisInputWords 16).map (fun inputs =>
    ((axisInputWords 13).map (fun other => f (inputScalarWord inputs) (inputScalarWord other))).sum)).sum =
    ((fourierOutcomes 256).map (fun a => ((fourierOutcomes 208).map (f a)).sum)).sum
  simp_rw [inputScalarWord_sum (A := State) 13]
  exact inputScalarWord_sum (A := State) 16 (fun a => ((fourierOutcomes 208).map (f a)).sum)

theorem stream_kernel_idealPointState (Q : Point) (x y : List Bool) :
    measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 17 (streamRawRightCalls Q))) y
      (measuredFourierKernel .inverse (streamFourierWires (indexedStreamCalls 1 (streamRawLeftCalls G Q))) x
        (Finsupp.lmapDomain ℂ ℂ (streamPreparedScalarOutput G Q) (streamPreparedEntry G Q))) =
      idealPointState Q (scalarRootFlip zeroBasisState) x y := by
  rw [streamFourierKernel_point_sum]
  simp only [List.smul_sum, List.map_map, Function.comp_def, smul_smul, idealPointState]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  apply congrArg (fun c : ℂ => c • ket (pointWrite (boolWordToNat a • G + boolWordToNat b • Q)
    (scalarRootFlip zeroBasisState)))
  rw [show (928 : Nat) = 464 + 464 by decide, pow_add]
  ring

theorem windowOutputPaths_zip (windows : List OddWindow) :
    windowOutputPaths windows = (axisInputWords windows.length).map (windows.zip ·) := by
  induction windows with
  | nil => rfl
  | cons w windows ih =>
    simp only [windowOutputPaths, List.length_cons, axisInputWords, List.map_flatMap,
      List.map_map, Function.comp_def, List.zip_cons_cons, ih]

/-- Expose both chronological output paths while preserving the terminal event. -/
theorem selectedIdealTwoAxes_paths_mass (Q : Point) (left right : List OddWindow)
    (terminal : List Bool → List Bool → Instrument) (ψ : State) :
    (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      ((fourierOutcomes 16).map (fun first =>
        ((windowOutputPaths left).map (fun lp =>
          ((windowOutputPaths right).map (fun rp =>
            (terminal ((lp.map Prod.snd).flatten.reverse ++ first.reverse)
              (rp.map Prod.snd).flatten.reverse).bornMass
                (actualAxisBranch Q rp List.nil (actualAxisBranch Q lp first.reverse
                  (fourierBranch .inverse streamAddress.reverse List.nil first
                    (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
                      (Quantum.run (streamAddress.map Gate.H) ψ))))))).sum)).sum)).sum := by
  have he : (selectedIdealTwoAxes Q left right terminal).bornMass ψ =
      (fourierContinuationInstrument List.nil (fun bits =>
        selectedIdealAxis Q left bits.reverse (fun lhs =>
          selectedIdealAxis Q right List.nil (terminal lhs)))).bornMass
        (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)
          (Quantum.run (streamAddress.map Gate.H) ψ)) := by
    simp only [selectedIdealTwoAxes, Instrument.bornMass, List.map_map, Function.comp_def,
      InstrumentBranch.seq, LinearMap.comp_apply]
  rw [he, fourierContinuationInstrument_mass]
  simp_rw [selectedIdealAxis_paths_mass]
  simp only [List.append_nil]

theorem selectedIdealTwoAxes_word_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (terminal : List Bool → List Bool → Instrument)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices terminal).bornMass (ket s) =
      ((axisInputWords 16).map (fun outputsL =>
        ((axisInputWords 13).map (fun outputsR =>
          (terminal outputsL.flatten.reverse outputsR.flatten.reverse).bornMass
            (idealPointState Q s outputsL.flatten outputsR.flatten))).sum)).sum := by
  rw [selectedIdealTwoAxes_paths_mass, windowOutputPaths_zip, windowOutputPaths_zip]
  simp only [show leftOddIndices.length = 15 by simp [leftOddIndices],
    show rightOddIndices.length = 13 by simp [rightOddIndices], List.map_map, Function.comp_def]
  rw [axisInputWords_sum_succ (A := ℝ) 15]
  apply congrArg List.sum
  apply List.map_congr_left
  intro firstOutput hf
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsL hlm
  apply congrArg List.sum
  apply List.map_congr_left
  intro outputsR hrm
  have hf' := (fourierOutcomes_mem 16 firstOutput).mp hf
  have hl' := (axisInputWords_mem 15 outputsL).mp hlm
  have hr' := (axisInputWords_mem 13 outputsR).mp hrm
  have hls : (leftOddIndices.zip outputsL).map Prod.snd = outputsL :=
    List.map_snd_zip (by simp only [leftOddIndices, List.length_ofFn, hl'.1, le_refl])
  have hrs : (rightOddIndices.zip outputsR).map Prod.snd = outputsR :=
    List.map_snd_zip (by simp only [rightOddIndices, List.length_ofFn, hr'.1, le_refl])
  rw [hls, hrs, actual_two_axes_input_state Q hQ hn firstOutput outputsL outputsR
    hf' hl'.1 hr'.1 hl'.2 hr'.2 s hs hz, twoAxisInputState_ideal]
  simp only [List.flatten_cons, List.reverse_append]

theorem outputWords_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : List Bool → A) :
    ((axisInputWords n).map (fun outputs => f outputs.flatten)).sum =
      ((fourierOutcomes (16 * n)).map f).sum := by
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun xs => (xs.map f).sum) (axisInputWords_flatten n)

/-- Exact output distribution of the full corrected 256/208-bit streaming
computation, expressed against an arbitrary output-dependent terminal instrument. -/
theorem selectedIdealTwoAxes_output_mass (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (terminal : List Bool → List Bool → Instrument)
    (s : BasisState) (hs : FirstWindowInput s) (hz : Clean streamAddress s) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices terminal).bornMass (ket s) =
      ((fourierOutcomes 256).map (fun lhs =>
        ((fourierOutcomes 208).map (fun rhs =>
          (terminal lhs.reverse rhs.reverse).bornMass (idealPointState Q s lhs rhs))).sum)).sum := by
  rw [selectedIdealTwoAxes_word_mass Q hQ hn terminal s hs hz]
  let f (lhs rhs : List Bool) : ℝ :=
    (terminal lhs.reverse rhs.reverse).bornMass (idealPointState Q s lhs rhs)
  change ((axisInputWords 16).map (fun outputs =>
    ((axisInputWords 13).map (fun other => f outputs.flatten other.flatten)).sum)).sum =
    ((fourierOutcomes 256).map (fun lhs => ((fourierOutcomes 208).map (f lhs)).sum)).sum
  simp_rw [outputWords_sum (A := ℝ) 13]
  exact outputWords_sum (A := ℝ) 16 (fun lhs => ((fourierOutcomes 208).map (f lhs)).sum)

private theorem port_IdealDistribution_unitary_prefix_mass (c : Circuit) (tail : AdaptiveCircuit) (ψ : State) :
    (AdaptiveCircuit.unitary c tail).run.bornMass ψ = tail.run.bornMass (Quantum.run c ψ) := by
  simp only [AdaptiveCircuit.run, Instrument.bornMass, List.map_map, Function.comp_def]
  rfl

theorem actual_terminal_mass (ψ : State) :
    (AdaptiveCircuit.unitary [.X 836]
      (measureResetWithCorrection batchedResetWires (fun _ => []))).run.bornMass ψ = normSq ψ := by
  calc
    _ = (measureResetWithCorrection batchedResetWires (fun _ => [])).run.bornMass
        (Quantum.run [.X 836] ψ) := port_IdealDistribution_unitary_prefix_mass _ _ _
    _ = normSq (Quantum.run [.X 836] ψ) := resetRegister_mass _ _
    _ = normSq ψ := normSq_run _ (by simp [CircuitWellFormed, Gate.WellFormed]) ψ

/-- The complete corrected streaming computation has exactly the ideal 256/208
Fourier event distribution, for any Boolean acceptance predicate. -/
theorem selectedIdealTwoAxes_event_eq (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (accept : Nat → Nat → Bool) :
    (selectedIdealTwoAxes Q leftOddIndices rightOddIndices (fun lhs rhs =>
      if accept (fourierWordLSB lhs.reverse) (fourierWordLSB rhs.reverse) then
        (AdaptiveCircuit.unitary [.X 836]
          (measureResetWithCorrection batchedResetWires (fun _ => []))).run
      else [])).bornMass (ket (zeroBasisState[836 ↦ true])) =
      reducedRawIdealFourierEventMass G Q (fun xy =>
        accept (fourierWordLSB xy.1) (fourierWordLSB xy.2)) := by
  rw [selectedIdealTwoAxes_output_mass Q hQ hn _ _ firstWindowInput_start
    (by
      intro v hv
      have hb : 855 ≤ v := by simpa [streamAddress, List.mem_range'_1] using (And.left (by
        simpa [streamAddress, List.mem_range'_1] using hv : 855 ≤ v ∧ v < 855 + 16))
      simp [upd, zeroBasisState, show v ≠ 836 by dsimp only [Wire] at *; omega])]
  rw [← streamIdealFourierEventMass_eq G Q G_ne_zero hn generator_nsmul_eq_zero hQ]
  unfold streamFourierKernelEventMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro lhs hl
  apply congrArg List.sum
  apply List.map_congr_left
  intro rhs hr
  simp only [List.reverse_reverse]
  split_ifs
  · rw [actual_terminal_mass, stream_kernel_idealPointState]
    rfl
  · rfl

end
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_IdealDistribution

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.FinalCertificate -/
section Port_FinalCertificate

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
attribute [local irreducible] batchedOuterPlan actualRoundSource streamingEntry

theorem publicPoint_order (Q : Point) (d : Nat) (h : Q=d • G) : order • Q=0 := by
  rw [h,smul_comm,generator_nsmul_eq_zero,nsmul_zero]

theorem actualRoundAcceptedMass_le_one (Q : Point) (hQ : order • Q=0) :
    Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) ≤ 1 := by
  exact (Instrument.bornMass_filter_le _ _ _).trans_eq (actualRoundSource_total Q hQ)

theorem actualCompiledRepeat_success_of_round (Q : Point) (hQ : order • Q=0) (hn : Q≠0)
    (h : (546:ℝ)/1000 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState)) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((((batchedOuterPlan.repeat streamingRounds 0).instantiate (readConstant coefficientAt Q) Fin.elim0).run).filter
        (fun b => (verifiedCandidate batchedOuterPlan.layoutForStreaming Q b.history).isSome)) (ket zeroBasisState) := by
  rw [actualCompiledRepeat_verified_mass Q hQ hn]
  have hm := independentRetrySuccessProbability_mono streamingRounds (actualRoundAcceptedMass_le_one Q hQ) h
  have hnum : (99:ℝ)/100 ≤ independentRetrySuccessProbability ((546:ℝ)/1000) streamingRounds := by
    norm_num [independentRetrySuccessProbability, streamingRounds]
  exact hnum.trans hm

/-- Actual single-round accepted mass, with the protected decoder and no loss term. -/
theorem streamingRound_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (546:ℝ)/1000 ≤ Instrument.bornMass ((actualRoundSource Q).run.filter
      (fun b => actualRoundFixedAccept (wrappedPairAccept legacyDecoderParams Q) b.history))
      (ket zeroBasisState) := by
  have hQ := publicPoint_order Q d hd
  rw [actualRoundSource_fixedPair_mass Q hQ hn,selectedIdealTwoAxes_event_eq Q hQ hn]
  exact wrappedIdeal_mass_lower Q G_ne_zero hn hQ d hd

/-- Success of the actual fixed 6-round entry, measured by the protected final decoder. -/
theorem streamingEntry_success (Q : Point) (d : Nat) (hn : Q≠0) (hd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass
      ((streamingEntry.instantiate Q).run.filter
        (fun b => (verifiedCandidate batchedOuterPlan.layoutForStreaming Q b.history).isSome))
      (ket zeroBasisState) := by
  rw [streamingEntry_instantiate]
  exact actualCompiledRepeat_success_of_round Q (publicPoint_order Q d hd) hn
    (streamingRound_success Q d hn hd)

/-- Unconditional protected certificate for the actual fixed streaming submission. -/
theorem streamingEntry_certificate_unconditional :
    Certificate officialLimits batchedOuterPlan.layoutForStreaming streamingEntry streamingBounds :=
  streamingEntry_certificate streamingEntry_success
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_FinalCertificate

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.FourierDirection -/
section Port_FourierDirection

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
-- Chronological emitted bits: the first measurement has weight 1.
example : readWord (true :: List.replicate 15 false) (List.range 16) = some 1 := by decide +kernel
example : fourierWordLSB (true :: List.replicate 15 false) = 1 := by decide +kernel
-- The last measurement has weight 2^15, not weight 1.
example : readWord (List.replicate 15 false ++ [true]) (List.range 16) = some 32768 := by decide +kernel
example : fourierWordLSB (List.replicate 15 false ++ [true]) = 32768 := by decide +kernel
-- The physical Fourier branch uses precisely that integer in its kernel exponent.
example (s : BasisState) :
    fourierBranch .inverse streamAddress.reverse List.nil (true :: List.replicate 15 false) (ket s) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^16) *
        dyadicFourierKernel .inverse 16 (fourierWordMSB (streamAddress.reverse.map s)) 1) •
        ket (fourierClear streamAddress.reverse s) := by
  simpa only [show streamAddress.reverse.length = 16 by decide +kernel,
    show fourierWordLSB (true :: List.replicate 15 false) = 1 by decide +kernel] using
    fourierBranch_ket_kernel .inverse streamAddress.reverse (by decide +kernel)
      (true :: List.replicate 15 false) (by decide +kernel) s
example (s : BasisState) :
    fourierBranch .inverse streamAddress.reverse List.nil (List.replicate 15 false ++ [true]) (ket s) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^16) *
        dyadicFourierKernel .inverse 16 (fourierWordMSB (streamAddress.reverse.map s)) 32768) •
        ket (fourierClear streamAddress.reverse s) := by
  simpa only [show streamAddress.reverse.length = 16 by decide +kernel,
    show fourierWordLSB (List.replicate 15 false ++ [true]) = 32768 by decide +kernel] using
    fourierBranch_ket_kernel .inverse streamAddress.reverse (by decide +kernel)
      (List.replicate 15 false ++ [true]) (by decide +kernel) s
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_FourierDirection

namespace ShorECDLP.Entrant
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

def entry := streamingEntry
def layout := batchedOuterPlan.layoutForStreaming
def bounds := streamingBounds

theorem certificate : Certificate officialLimits layout entry bounds :=
  streamingEntry_certificate_unconditional

end ShorECDLP.Entrant
