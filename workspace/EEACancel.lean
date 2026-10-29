import ShorECDLP.Submission.Entrant.Streaming.Correction

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem run_ccx_twice (a b t : Wire) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ψ : State) :
    Quantum.run [.CCX a b t, .CCX a b t] ψ = ψ := by
  have h := run_adjoint_run ([.CCX a b t] : Circuit) (by
    simp only [CircuitWellFormed, List.mem_singleton]
    intro g hg
    subst g
    exact ⟨hab, hat, hbt⟩) ψ
  simpa using h

def sameCCX : Gate → Gate → Bool
  | .CCX a b t, .CCX a' b' t' => a = a' && b = b' && t = t'
  | _, _ => false

/-- Cancel disjoint adjacent CCX pairs at even offsets.  A second offset pass
finds the odd-offset pairs in the EEA boundary circuits. -/
def cancelEvenCCX : Circuit → Circuit
  | g :: h :: gs => if sameCCX g h then cancelEvenCCX gs else g :: h :: cancelEvenCCX gs
  | gs => gs

def cancelOddCCX : Circuit → Circuit
  | g :: gs => g :: cancelEvenCCX gs
  | [] => []

def cancelBoundaryCCX (gs : Circuit) : Circuit := cancelOddCCX (cancelEvenCCX gs)

theorem run_sameCCX (g h : Gate) (heq : sameCCX g h = true)
    (hwf : g.WellFormed) (ψ : State) : Quantum.run [g, h] ψ = ψ := by
  cases g <;> cases h <;> simp [sameCCX] at heq
  case CCX.CCX a b t a' b' t' =>
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := heq
    subst a'
    subst b'
    subst t'
    exact run_ccx_twice a b t hwf.1 hwf.2.1 hwf.2.2 ψ

theorem cancelEvenCCX_run (gs : Circuit) (hwf : CircuitWellFormed gs) (ψ : State) :
    Quantum.run (cancelEvenCCX gs) ψ = Quantum.run gs ψ := by
  induction gs using cancelEvenCCX.induct generalizing ψ with
  | case1 g h gs heq ih =>
      simp only [cancelEvenCCX, heq, if_true]
      rw [ih]
      · simp only [run_cons]
        exact congrArg (run gs) (run_sameCCX g h heq (hwf g (by simp)) ψ).symm
      · intro k hk
        exact hwf k (by simp [hk])
  | case2 g h gs heq ih =>
      have hfalse : sameCCX g h = false := Bool.eq_false_of_not_eq_true heq
      simp only [cancelEvenCCX, hfalse, Bool.false_eq_true, if_false, run_cons]
      rw [ih]
      intro k hk
      exact hwf k (by simp [hk])
  | case3 gs hshort =>
      cases gs with
      | nil => rfl
      | cons g gs =>
          cases gs with
          | nil => rfl
          | cons h gs => exact (hshort g h gs rfl).elim

theorem cancelEvenCCX_subset (gs : Circuit) : cancelEvenCCX gs ⊆ gs := by
  induction gs using cancelEvenCCX.induct with
  | case1 g h gs heq ih =>
      simp only [cancelEvenCCX, heq, if_true]
      exact ih.trans (by simp)
  | case2 g h gs heq ih =>
      have hfalse : sameCCX g h = false := Bool.eq_false_of_not_eq_true heq
      simp only [cancelEvenCCX, hfalse, Bool.false_eq_true, if_false]
      intro k hk
      simp only [List.mem_cons] at hk ⊢
      rcases hk with rfl | rfl | hk
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (ih hk))
  | case3 gs hshort =>
      cases gs with
      | nil => exact List.Subset.refl []
      | cons g gs =>
          cases gs with
          | nil => exact List.Subset.refl [g]
          | cons h gs => exact (hshort g h gs rfl).elim

theorem cancelOddCCX_run (gs : Circuit) (hwf : CircuitWellFormed gs) (ψ : State) :
    Quantum.run (cancelOddCCX gs) ψ = Quantum.run gs ψ := by
  cases gs with
  | nil => rfl
  | cons g gs =>
      simp only [cancelOddCCX, run_cons]
      rw [cancelEvenCCX_run]
      intro k hk
      exact hwf k (by simp [hk])

theorem cancelBoundaryCCX_run (gs : Circuit) (hwf : CircuitWellFormed gs) (ψ : State) :
    Quantum.run (cancelBoundaryCCX gs) ψ = Quantum.run gs ψ := by
  rw [cancelBoundaryCCX, cancelOddCCX_run]
  · exact cancelEvenCCX_run gs hwf ψ
  · intro g hg
    exact hwf g (cancelEvenCCX_subset gs hg)

def productionEPrefix : Circuit :=
  ((computeControl [indexedStepProductionRegisters.phase2,
      indexedStepProductionRegisters.sign] 2 indexedStepProductionRegisters.terminal
      indexedStepProductionRegisters.blockScratch ++
    computeControl [indexedStepProductionRegisters.phase1,
      indexedStepProductionRegisters.terminal] 1 indexedStepProductionRegisters.control
      indexedStepProductionRegisters.blockScratch) ++
    computeControl [indexedStepProductionRegisters.phase2,
      indexedStepProductionRegisters.sign] 2 indexedStepProductionRegisters.terminal
      indexedStepProductionRegisters.blockScratch) ++
    prepareLatestPaperTBoundary indexedStepProductionRegisters.tBoundary 256

def productionESuffix : Circuit :=
  computeControl [indexedStepProductionRegisters.phase1] 1
    indexedStepProductionRegisters.control indexedStepProductionRegisters.blockScratch ++
    restoreLatestPaperTBoundary indexedStepProductionRegisters.tBoundary 256

example : CircuitWellFormed productionEPrefix := by
  simp only [productionEPrefix, circuitWellFormed_append]
  exact ⟨⟨⟨
    computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientTemporary,
    computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientSub⟩,
    computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientTemporary⟩,
    prepareLatestPaperTBoundary_wellFormed _ 256 indexedStepProduction_layout.tBoundary⟩
example : CircuitWellFormed productionESuffix := by
  simp only [productionESuffix, circuitWellFormed_append]
  exact ⟨computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientAdd,
    restoreLatestPaperTBoundary_wellFormed _ 256 indexedStepProduction_layout.tBoundary⟩

set_option maxRecDepth 100000 in
theorem productionEPrefix_cancel_tCount :
    ShorECDLP.tCount (cancelBoundaryCCX productionEPrefix) + 42 =
    ShorECDLP.tCount productionEPrefix := by rfl
set_option maxRecDepth 100000 in
theorem productionESuffix_cancel_tCount :
    ShorECDLP.tCount (cancelBoundaryCCX productionESuffix) + 42 =
    ShorECDLP.tCount productionESuffix := by rfl

theorem unitary_run_cancelBoundaryCCX (gs : Circuit) (hwf : CircuitWellFormed gs) :
    (AdaptiveCircuit.unitary (cancelBoundaryCCX gs) .done).run =
      (AdaptiveCircuit.unitary gs .done).run := by
  simp only [AdaptiveCircuit.run]
  congr 2
  exact LinearMap.ext (fun ψ ↦ cancelBoundaryCCX_run gs hwf ψ)

def productionEMiddle : Circuit :=
  (((computeControl [indexedStepProductionRegisters.phase2,
      indexedStepProductionRegisters.sign] 2 indexedStepProductionRegisters.terminal
      indexedStepProductionRegisters.blockScratch ++
    computeControl [indexedStepProductionRegisters.phase1,
      indexedStepProductionRegisters.terminal] 1 indexedStepProductionRegisters.control
      indexedStepProductionRegisters.blockScratch) ++
    computeControl [indexedStepProductionRegisters.phase2,
      indexedStepProductionRegisters.sign] 2 indexedStepProductionRegisters.terminal
      indexedStepProductionRegisters.blockScratch) ++
    [.CX indexedStepProductionRegisters.phase1 indexedStepProductionRegisters.sign]) ++
    computeControl [indexedStepProductionRegisters.phase1] 1
      indexedStepProductionRegisters.control indexedStepProductionRegisters.blockScratch

def optimizedEPrefixSegment (n cursor : Nat) :
    (count : Nat) × Straight n cursor (cursor + count) :=
  ⟨0, literalProgram (cancelBoundaryCCX productionEPrefix)⟩

def optimizedEMiddleSegment (n cursor : Nat) :
    (count : Nat) × Straight n cursor (cursor + count) :=
  ⟨0, literalProgram productionEMiddle⟩

def optimizedESuffixSegment (n cursor : Nat) :
    (count : Nat) × Straight n cursor (cursor + count) :=
  ⟨0, literalProgram (cancelBoundaryCCX productionESuffix)⟩

def optimizedCoefficientSegments (n T : Nat) : List (FixedSegment n) :=
  let r := indexedStepProductionRegisters;
  let w := (certifiedActiveWindows 256 T).coefficient;
  [optimizedEPrefixSegment n,
    (fun cursor ↦ coefficientProgram n cursor (r.coefficient w) w.start w.stop .sub false .work2),
    optimizedEMiddleSegment n,
    (fun cursor ↦ coefficientProgram n cursor (r.coefficient w) w.start w.stop .add true .work2),
    optimizedESuffixSegment n]

def optimizedCoefficientProgram (n start T : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (optimizedCoefficientSegments n T) start

def optimizedCoefficientAdaptive (T : Nat) : AdaptiveCircuit :=
  let r := indexedStepProductionRegisters
  let w := (certifiedActiveWindows 256 T).coefficient
  sequenceCircuit [
    .unitary (cancelBoundaryCCX productionEPrefix) .done,
    coefficientPrefixAdaptive (r.coefficient w) w.start w.stop .sub false .work2,
    .unitary productionEMiddle .done,
    coefficientPrefixAdaptive (r.coefficient w) w.start w.stop .add true .work2,
    .unitary (cancelBoundaryCCX productionESuffix) .done]

theorem optimizedCoefficientProgram_run_source (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedCoefficientProgram n start T) read history =
      (optimizedCoefficientAdaptive T).run := by
  unfold optimizedCoefficientProgram optimizedCoefficientAdaptive
  apply sequenceProgram_run
  unfold optimizedCoefficientSegments
  dsimp only
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
  · intro cursor hist
    simp only [optimizedEPrefixSegment, compiledRun]
    exact literalProgram_run _ read hist
  · intro cursor hist
    exact coefficientProgram_run n cursor _ _ _ .sub false .work2 read hist
  · intro cursor hist
    simp only [optimizedEMiddleSegment, compiledRun]
    exact literalProgram_run _ read hist
  · intro cursor hist
    exact coefficientProgram_run n cursor _ _ _ .add true .work2 read hist
  · intro cursor hist
    simp only [optimizedESuffixSegment, compiledRun]
    exact literalProgram_run _ read hist

theorem optimizedCoefficientProgram_run (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedCoefficientProgram n start T) read history =
      (blockEAdaptive indexedStepProductionRegisters 256
        (certifiedActiveWindows 256 T).coefficient).run := by
  let r := indexedStepProductionRegisters
  let w := (certifiedActiveWindows 256 T).coefficient
  rw [← coefficientBlockSources_eq r 256 w]
  apply sequenceProgram_run
  unfold optimizedCoefficientSegments coefficientBlockSources
  dsimp only [r, w]
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
  · intro cursor h
    simp only [optimizedEPrefixSegment, compiledRun]
    rw [literalProgram_run]
    exact unitary_run_cancelBoundaryCCX productionEPrefix (by
      simp only [productionEPrefix, circuitWellFormed_append]
      exact ⟨⟨⟨
        computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientTemporary,
        computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientSub⟩,
        computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientTemporary⟩,
        prepareLatestPaperTBoundary_wellFormed _ 256 indexedStepProduction_layout.tBoundary⟩)
  · intro cursor h
    exact coefficientProgram_run n cursor _ _ _ .sub false .work2 read h
  · intro cursor h
    simpa only [productionEMiddle] using literalProgram_run productionEMiddle read h
  · intro cursor h
    exact coefficientProgram_run n cursor _ _ _ .add true .work2 read h
  · intro cursor h
    simp only [optimizedESuffixSegment, compiledRun]
    rw [literalProgram_run]
    exact unitary_run_cancelBoundaryCCX productionESuffix (by
      simp only [productionESuffix, circuitWellFormed_append]
      exact ⟨computeControl_wellFormed _ _ _ _ indexedStepProduction_layout.coefficientAdd,
        restoreLatestPaperTBoundary_wellFormed _ 256 indexedStepProduction_layout.tBoundary⟩)

theorem optimizedCoefficientAdaptive_run (T : Nat) :
    (optimizedCoefficientAdaptive T).run =
      (blockEAdaptive indexedStepProductionRegisters 256
        (certifiedActiveWindows 256 T).coefficient).run := by
  rw [← optimizedCoefficientProgram_run_source 1 0 T (fun _ ↦ false) Fin.elim0]
  exact optimizedCoefficientProgram_run 1 0 T (fun _ ↦ false) Fin.elim0

theorem productionCoefficientBlockSources (T : Nat) :
    coefficientBlockSources indexedStepProductionRegisters 256
      (certifiedActiveWindows 256 T).coefficient = [
        .unitary productionEPrefix .done,
        coefficientPrefixAdaptive
          (indexedStepProductionRegisters.coefficient
            (certifiedActiveWindows 256 T).coefficient)
          (certifiedActiveWindows 256 T).coefficient.start
          (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2,
        .unitary productionEMiddle .done,
        coefficientPrefixAdaptive
          (indexedStepProductionRegisters.coefficient
            (certifiedActiveWindows 256 T).coefficient)
          (certifiedActiveWindows 256 T).coefficient.start
          (certifiedActiveWindows 256 T).coefficient.stop .add true .work2,
        .unitary productionESuffix .done] := by
  rfl

attribute [local irreducible] productionEPrefix productionEMiddle productionESuffix
  cancelBoundaryCCX

theorem optimizedCoefficientProgram_tCount_formula (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedCoefficientProgram n start T) read history =
      (sequenceCircuit ([
        .unitary (cancelBoundaryCCX productionEPrefix) .done,
        coefficientPrefixAdaptive
          (indexedStepProductionRegisters.coefficient
            (certifiedActiveWindows 256 T).coefficient)
          (certifiedActiveWindows 256 T).coefficient.start
          (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2,
        .unitary productionEMiddle .done,
        coefficientPrefixAdaptive
          (indexedStepProductionRegisters.coefficient
            (certifiedActiveWindows 256 T).coefficient)
          (certifiedActiveWindows 256 T).coefficient.start
          (certifiedActiveWindows 256 T).coefficient.stop .add true .work2,
        .unitary (cancelBoundaryCCX productionESuffix) .done] : List AdaptiveCircuit)).tCount := by
  unfold optimizedCoefficientProgram
  apply sequenceProgram_tCount
  unfold optimizedCoefficientSegments
  dsimp only
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
  · intro cursor hist
    simp only [optimizedEPrefixSegment, compiledTCount]
    exact literalProgram_tCount _ read hist
  · intro cursor hist
    exact coefficientProgram_tCount n cursor _ _ _ .sub false .work2 read hist
  · intro cursor hist
    simp only [optimizedEMiddleSegment, compiledTCount]
    exact literalProgram_tCount _ read hist
  · intro cursor hist
    exact coefficientProgram_tCount n cursor _ _ _ .add true .work2 read hist
  · intro cursor hist
    simp only [optimizedESuffixSegment, compiledTCount]
    exact literalProgram_tCount _ read hist

theorem fiveSegment_tCount (pre mid suf : Circuit) (first second : AdaptiveCircuit) :
    (sequenceCircuit ([.unitary pre .done, first, .unitary mid .done,
      second, .unitary suf .done] : List AdaptiveCircuit)).tCount =
      ShorECDLP.tCount pre + first.tCount + ShorECDLP.tCount mid +
        second.tCount + ShorECDLP.tCount suf := by
  simp only [sequenceCircuit, adaptive_tCount_seq, AdaptiveCircuit.tCount]
  omega

theorem productionCoefficientSource_tCount (T : Nat) :
    (blockEAdaptive indexedStepProductionRegisters 256
      (certifiedActiveWindows 256 T).coefficient).tCount =
      ShorECDLP.tCount productionEPrefix +
        (coefficientPrefixAdaptive
          (indexedStepProductionRegisters.coefficient
            (certifiedActiveWindows 256 T).coefficient)
          (certifiedActiveWindows 256 T).coefficient.start
          (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2).tCount +
        ShorECDLP.tCount productionEMiddle +
        (coefficientPrefixAdaptive
          (indexedStepProductionRegisters.coefficient
            (certifiedActiveWindows 256 T).coefficient)
          (certifiedActiveWindows 256 T).coefficient.start
          (certifiedActiveWindows 256 T).coefficient.stop .add true .work2).tCount +
        ShorECDLP.tCount productionESuffix := by
  rw [← coefficientBlockSources_eq indexedStepProductionRegisters 256
    (certifiedActiveWindows 256 T).coefficient]
  rw [productionCoefficientBlockSources T]
  exact fiveSegment_tCount _ _ _ _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem optimizedCoefficientProgram_tCount (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedCoefficientProgram n start T) read history + 84 =
      (blockEAdaptive indexedStepProductionRegisters 256
        (certifiedActiveWindows 256 T).coefficient).tCount := by
  rw [optimizedCoefficientProgram_tCount_formula n start T read history]
  rw [fiveSegment_tCount]
  rw [productionCoefficientSource_tCount T]
  have hp := productionEPrefix_cancel_tCount
  have hs := productionESuffix_cancel_tCount
  omega

theorem optimizedCoefficientAdaptive_tCount (T : Nat) :
    (optimizedCoefficientAdaptive T).tCount + 84 =
      (blockEAdaptive indexedStepProductionRegisters 256
        (certifiedActiveWindows 256 T).coefficient).tCount := by
  have h := optimizedCoefficientProgram_tCount 1 0 T (fun _ ↦ false) Fin.elim0
  rw [optimizedCoefficientProgram_tCount_formula] at h
  simpa only [optimizedCoefficientAdaptive] using h

def optimizedMeasuredStepSources (T : Nat) : List AdaptiveCircuit :=
  let r := indexedStepProductionRegisters;
  [.unitary (blockAForward r) .done,
    blockBAdaptive r 256 (certifiedActiveWindows 256 T).remainder,
    .unitary (blockCForward r ++
      blockDForward r (certifiedActiveWindows 256 T).quotientSwap) .done,
    optimizedCoefficientAdaptive T,
    .unitary (blockFForward r) .done,
    phaseUpdateEpochAdaptive r.phaseUpdate r.shiftEpoch,
    measuredBlockHForward r 256 T]

def optimizedMeasuredStepSegments (n T : Nat) : List (FixedSegment n) :=
  let r := indexedStepProductionRegisters;
  [(fun _ ↦ ⟨0, literalProgram (blockAForward r)⟩),
    (fun cursor ↦ remainderBlockProgram n cursor r 256
      (certifiedActiveWindows 256 T).remainder),
    (fun _ ↦ ⟨0, literalProgram (blockCForward r ++
      blockDForward r (certifiedActiveWindows 256 T).quotientSwap)⟩),
    (fun cursor ↦ optimizedCoefficientProgram n cursor T),
    (fun _ ↦ ⟨0, literalProgram (blockFForward r)⟩),
    (fun cursor ↦ phaseProgram n cursor r.phaseUpdate r.shiftEpoch),
    (fun cursor ↦ hProgram n cursor r 256 T)]

def optimizedMeasuredStepProgram (n start T : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  sequenceProgram n (optimizedMeasuredStepSegments n T) start

theorem optimizedMeasuredStepProgram_run (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedMeasuredStepProgram n start T) read history =
      (measuredIndexedStep indexedStepProductionRegisters 256 T).run := by
  unfold optimizedMeasuredStepProgram
  rw [sequenceProgram_run n (optimizedMeasuredStepSegments n T)
    (optimizedMeasuredStepSources T) read]
  · rw [← measuredStepSources_eq indexedStepProductionRegisters 256 T]
    simp only [optimizedMeasuredStepSources, measuredStepSources, sequenceCircuit,
      AdaptiveCircuit.run_seq, optimizedCoefficientAdaptive_run]
  · unfold optimizedMeasuredStepSegments optimizedMeasuredStepSources
    dsimp only
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
        (List.Forall₂.cons ?_ List.Forall₂.nil))))))
    · intro cursor hist; exact literalCompiled_run _ read hist
    · intro cursor hist; exact remainderBlockProgram_run n cursor _ 256 _ read hist
    · intro cursor hist; exact literalCompiled_run _ read hist
    · intro cursor hist; exact optimizedCoefficientProgram_run_source n cursor T read hist
    · intro cursor hist; exact literalCompiled_run _ read hist
    · intro cursor hist; exact phaseProgram_run n cursor _ _ read hist
    · intro cursor hist; exact hProgram_run n cursor _ 256 T read hist

theorem optimizedMeasuredStepProgram_tCount (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedMeasuredStepProgram n start T) read history + 84 =
      (measuredIndexedStep indexedStepProductionRegisters 256 T).tCount := by
  let sources := optimizedMeasuredStepSources T
  have hs : List.Forall₂ (fun p source ↦ ∀ cursor hist,
      compiledTCount (p cursor) read hist = source.tCount)
      (optimizedMeasuredStepSegments n T) sources := by
    dsimp only [sources]
    unfold optimizedMeasuredStepSegments optimizedMeasuredStepSources
    dsimp only
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
        (List.Forall₂.cons ?_ List.Forall₂.nil))))))
    · intro cursor hist; exact literalCompiled_tCount _ read hist
    · intro cursor hist; exact remainderBlockProgram_tCount n cursor _ 256 _ read hist
    · intro cursor hist; exact literalCompiled_tCount _ read hist
    · intro cursor hist
      rw [optimizedCoefficientProgram_tCount_formula n cursor T read hist]
      rfl
    · intro cursor hist; exact literalCompiled_tCount _ read hist
    · intro cursor hist; exact phaseProgram_tCount n cursor _ _ read hist
    · intro cursor hist; exact hProgram_tCount n cursor _ 256 T read hist
  unfold optimizedMeasuredStepProgram
  rw [sequenceProgram_tCount n (optimizedMeasuredStepSegments n T) sources read hs start history]
  dsimp only [sources]
  unfold optimizedMeasuredStepSources
  rw [← measuredStepSources_eq indexedStepProductionRegisters 256 T]
  simp only [measuredStepSources, sequenceCircuit,
    adaptive_tCount_seq]
  have hc := optimizedCoefficientAdaptive_tCount T
  omega

def optimizedMeasuredStepAdaptive (T : Nat) : AdaptiveCircuit :=
  sequenceCircuit (optimizedMeasuredStepSources T)

theorem optimizedMeasuredStepProgram_run_source (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedMeasuredStepProgram n start T) read history =
      (optimizedMeasuredStepAdaptive T).run := by
  unfold optimizedMeasuredStepProgram optimizedMeasuredStepAdaptive
  apply sequenceProgram_run
  unfold optimizedMeasuredStepSegments optimizedMeasuredStepSources
  dsimp only
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ List.Forall₂.nil))))))
  · intro cursor hist; exact literalCompiled_run _ read hist
  · intro cursor hist; exact remainderBlockProgram_run n cursor _ 256 _ read hist
  · intro cursor hist; exact literalCompiled_run _ read hist
  · intro cursor hist; exact optimizedCoefficientProgram_run_source n cursor T read hist
  · intro cursor hist; exact literalCompiled_run _ read hist
  · intro cursor hist; exact phaseProgram_run n cursor _ _ read hist
  · intro cursor hist; exact hProgram_run n cursor _ 256 T read hist

theorem optimizedMeasuredStepProgram_tCount_source (n start T : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedMeasuredStepProgram n start T) read history =
      (optimizedMeasuredStepAdaptive T).tCount := by
  unfold optimizedMeasuredStepProgram optimizedMeasuredStepAdaptive
  apply sequenceProgram_tCount
  unfold optimizedMeasuredStepSegments optimizedMeasuredStepSources
  dsimp only
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ List.Forall₂.nil))))))
  · intro cursor hist; exact literalCompiled_tCount _ read hist
  · intro cursor hist; exact remainderBlockProgram_tCount n cursor _ 256 _ read hist
  · intro cursor hist; exact literalCompiled_tCount _ read hist
  · intro cursor hist
    rw [optimizedCoefficientProgram_tCount_formula n cursor T read hist]
    rfl
  · intro cursor hist; exact literalCompiled_tCount _ read hist
  · intro cursor hist; exact phaseProgram_tCount n cursor _ _ read hist
  · intro cursor hist; exact hProgram_tCount n cursor _ 256 T read hist

theorem optimizedMeasuredStepAdaptive_run (T : Nat) :
    (optimizedMeasuredStepAdaptive T).run =
      (measuredIndexedStep indexedStepProductionRegisters 256 T).run := by
  rw [← optimizedMeasuredStepProgram_run_source 1 0 T (fun _ ↦ false) Fin.elim0]
  exact optimizedMeasuredStepProgram_run 1 0 T (fun _ ↦ false) Fin.elim0

theorem optimizedMeasuredStepAdaptive_tCount (T : Nat) :
    (optimizedMeasuredStepAdaptive T).tCount + 84 =
      (measuredIndexedStep indexedStepProductionRegisters 256 T).tCount := by
  have h := optimizedMeasuredStepProgram_tCount 1 0 T (fun _ ↦ false) Fin.elim0
  rw [optimizedMeasuredStepProgram_tCount_source] at h
  exact h

def optimizedMeasuredScheduleAdaptive : Nat → Nat → AdaptiveCircuit
  | 0, _ => .done
  | count + 1, first =>
      (optimizedMeasuredStepAdaptive first).seq
        (optimizedMeasuredScheduleAdaptive count (first + 1))

def optimizedMeasuredScheduleProgram (n : Nat) :
    (count first start : Nat) → (events : Nat) × Straight n start (start+events)
  | 0, _, _ => ⟨0, literalProgram []⟩
  | count + 1, first, start =>
      let step := optimizedMeasuredStepProgram n start first
      appendCompiled step
        (optimizedMeasuredScheduleProgram n count (first+1) (start+step.1))

theorem optimizedMeasuredScheduleProgram_run (n count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedMeasuredScheduleProgram n count first start) read history =
      (optimizedMeasuredScheduleAdaptive count first).run := by
  induction count generalizing first start with
  | zero => exact literalProgram_run [] read history
  | succ count ih =>
      unfold optimizedMeasuredScheduleProgram optimizedMeasuredScheduleAdaptive
      dsimp only
      apply appendCompiled_run_eq
      · exact optimizedMeasuredStepProgram_run_source n start first read history
      · intro h
        exact ih (first+1) _ h

theorem optimizedMeasuredScheduleAdaptive_run (count first : Nat) :
    (optimizedMeasuredScheduleAdaptive count first).run =
      (measuredIndexedSchedule indexedStepProductionRegisters 256 first count).run := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      unfold optimizedMeasuredScheduleAdaptive measuredIndexedSchedule
      rw [AdaptiveCircuit.run_seq, AdaptiveCircuit.run_seq,
        optimizedMeasuredStepAdaptive_run, ih]

theorem optimizedMeasuredScheduleProgram_tCount (n count first start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedMeasuredScheduleProgram n count first start) read history =
      (optimizedMeasuredScheduleAdaptive count first).tCount := by
  induction count generalizing first start with
  | zero => rfl
  | succ count ih =>
      unfold optimizedMeasuredScheduleProgram optimizedMeasuredScheduleAdaptive
      dsimp only
      apply appendCompiled_tCount_eq
      · exact optimizedMeasuredStepProgram_tCount_source n start first read history
      · intro h
        exact ih (first+1) _ h

theorem optimizedMeasuredScheduleAdaptive_tCount (count first : Nat) :
    (optimizedMeasuredScheduleAdaptive count first).tCount + 84 * count =
      (measuredIndexedSchedule indexedStepProductionRegisters 256 first count).tCount := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      unfold optimizedMeasuredScheduleAdaptive measuredIndexedSchedule
      simp only [adaptive_tCount_seq]
      have hs := optimizedMeasuredStepAdaptive_tCount first
      have ht := ih (first+1)
      omega

def optimizedEEAForwardAdaptive : AdaptiveCircuit :=
  optimizedMeasuredScheduleAdaptive secp256k1ScheduleLength 1

def optimizedEEAForwardProgram (n start : Nat) :
    (events : Nat) × Straight n start (start+events) :=
  optimizedMeasuredScheduleProgram n secp256k1ScheduleLength 1 start

theorem optimizedEEAForwardProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedEEAForwardProgram n start) read history =
      optimizedEEAForwardAdaptive.run :=
  optimizedMeasuredScheduleProgram_run n secp256k1ScheduleLength 1 start read history

theorem optimizedEEAForwardAdaptive_run :
    optimizedEEAForwardAdaptive.run =
      (secp256k1MeasuredEEAForward indexedStepProductionRegisters).run := by
  exact optimizedMeasuredScheduleAdaptive_run secp256k1ScheduleLength 1

theorem optimizedEEAForwardProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedEEAForwardProgram n start) read history =
      optimizedEEAForwardAdaptive.tCount :=
  optimizedMeasuredScheduleProgram_tCount n secp256k1ScheduleLength 1 start read history

theorem optimizedEEAForwardAdaptive_eq :
    optimizedEEAForwardAdaptive =
      optimizedMeasuredScheduleAdaptive secp256k1ScheduleLength 1 := rfl

theorem secp256k1MeasuredEEAForward_eq :
    secp256k1MeasuredEEAForward indexedStepProductionRegisters =
      measuredIndexedSchedule indexedStepProductionRegisters 256 1
        secp256k1ScheduleLength := rfl

attribute [local irreducible] optimizedEEAForwardAdaptive secp256k1MeasuredEEAForward

theorem optimizedEEAForwardAdaptive_tCount :
    optimizedEEAForwardAdaptive.tCount + 84 * secp256k1ScheduleLength =
      (secp256k1MeasuredEEAForward indexedStepProductionRegisters).tCount := by
  have h := optimizedMeasuredScheduleAdaptive_tCount secp256k1ScheduleLength 1
  have ho := congrArg AdaptiveCircuit.tCount optimizedEEAForwardAdaptive_eq
  have hm := congrArg AdaptiveCircuit.tCount secp256k1MeasuredEEAForward_eq
  rw [ho, hm]
  exact h

def optimizedForwardWrapperSources : List AdaptiveCircuit :=
  [eeaPreprocess,
    optimizedEEAForwardAdaptive,
    .unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done,
    secp256k1EEAParityCorrection,
    .unitary terminalWork1Clear .done]

def optimizedForwardWrapperSegments (n : Nat) : List (FixedSegment n) :=
  [(fun cursor ↦ preprocessProgram n cursor),
    (fun cursor ↦ optimizedEEAForwardProgram n cursor),
    (fun _ ↦ ⟨0, literalProgram (canonicalWork2Rotation ++ terminalEpochCompression)⟩),
    (fun cursor ↦ productionParityProgram n cursor),
    (fun _ ↦ ⟨0, literalProgram terminalWork1Clear⟩)]

def optimizedForwardWrapperProgram (n start : Nat) :
    (events : Nat) × Straight n start (start+events) :=
  sequenceProgram n (optimizedForwardWrapperSegments n) start

def optimizedForwardWrapperAdaptive : AdaptiveCircuit :=
  sequenceCircuit optimizedForwardWrapperSources

theorem optimizedForwardWrapperProgram_run_source (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedForwardWrapperProgram n start) read history =
      optimizedForwardWrapperAdaptive.run := by
  unfold optimizedForwardWrapperProgram optimizedForwardWrapperAdaptive
  apply sequenceProgram_run
  unfold optimizedForwardWrapperSegments optimizedForwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
  · intro cursor hist; exact preprocessProgram_run n cursor read hist
  · intro cursor hist; exact optimizedEEAForwardProgram_run n cursor read hist
  · intro cursor hist; exact literalCompiled_run _ read hist
  · intro cursor hist; exact productionParityProgram_run n cursor read hist
  · intro cursor hist; exact literalCompiled_run _ read hist

theorem optimizedForwardWrapperAdaptive_run :
    optimizedForwardWrapperAdaptive.run = secp256k1MeasuredEEAForwardWrapper.run := by
  rw [← measuredForwardWrapperSources_eq]
  simp only [optimizedForwardWrapperAdaptive, optimizedForwardWrapperSources,
    measuredForwardWrapperSources, sequenceCircuit, AdaptiveCircuit.run_seq,
    optimizedEEAForwardAdaptive_run]

theorem optimizedForwardWrapperProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedForwardWrapperProgram n start) read history =
      secp256k1MeasuredEEAForwardWrapper.run :=
  (optimizedForwardWrapperProgram_run_source n start read history).trans
    optimizedForwardWrapperAdaptive_run

theorem sequence5_tCount (a b c d e : AdaptiveCircuit) :
    (sequenceCircuit [a,b,c,d,e]).tCount =
      a.tCount + b.tCount + c.tCount + d.tCount + e.tCount := by
  simp only [sequenceCircuit, adaptive_tCount_seq, AdaptiveCircuit.tCount]
  omega

theorem optimizedForwardWrapperProgram_tCount_source (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedForwardWrapperProgram n start) read history =
      optimizedForwardWrapperAdaptive.tCount := by
  unfold optimizedForwardWrapperProgram optimizedForwardWrapperAdaptive
  apply sequenceProgram_tCount
  unfold optimizedForwardWrapperSegments optimizedForwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))))
  · intro cursor hist; exact preprocessProgram_tCount n cursor read hist
  · intro cursor hist; exact optimizedEEAForwardProgram_tCount n cursor read hist
  · intro cursor hist; exact literalCompiled_tCount _ read hist
  · intro cursor hist; exact productionParityProgram_tCount n cursor read hist
  · intro cursor hist; exact literalCompiled_tCount _ read hist

theorem optimizedForwardWrapperAdaptive_tCount :
    optimizedForwardWrapperAdaptive.tCount + 84 * secp256k1ScheduleLength =
      secp256k1MeasuredEEAForwardWrapper.tCount := by
  rw [← measuredForwardWrapperSources_eq]
  unfold measuredForwardWrapperSources
  rw [show optimizedForwardWrapperAdaptive.tCount =
      eeaPreprocess.tCount + optimizedEEAForwardAdaptive.tCount +
        (AdaptiveCircuit.unitary (canonicalWork2Rotation ++ terminalEpochCompression) .done).tCount +
        secp256k1EEAParityCorrection.tCount +
        (AdaptiveCircuit.unitary terminalWork1Clear .done).tCount by
      exact sequence5_tCount _ _ _ _ _]
  rw [sequence5_tCount]
  have h := optimizedEEAForwardAdaptive_tCount
  omega

theorem optimizedForwardWrapperProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedForwardWrapperProgram n start) read history +
        84 * secp256k1ScheduleLength =
      secp256k1MeasuredEEAForwardWrapper.tCount := by
  rw [optimizedForwardWrapperProgram_tCount_source]
  exact optimizedForwardWrapperAdaptive_tCount

def optimizedForwardDataBankProgram (n start : Nat) :
    (events : Nat) × Straight n start (start+events) :=
  relabelCompiled eeaWorkspaceExchange (optimizedForwardWrapperProgram n start)

theorem optimizedForwardDataBankProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedForwardDataBankProgram n start) read history =
      secp256k1MeasuredEEAForwardInDataBank.run := by
  exact relabelCompiled_run _ _ _ read history
    (optimizedForwardWrapperProgram_run n start read history)

theorem optimizedForwardDataBankProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedForwardDataBankProgram n start) read history +
        84 * secp256k1ScheduleLength =
      secp256k1MeasuredEEAForwardInDataBank.tCount := by
  have h := relabelCompiled_tCount eeaWorkspaceExchange
    (optimizedForwardWrapperProgram n start) optimizedForwardWrapperAdaptive read history
    (optimizedForwardWrapperProgram_tCount_source n start read history)
  unfold optimizedForwardDataBankProgram
  rw [h]
  simpa only [secp256k1MeasuredEEAForwardInDataBank,
    AdaptiveCircuit.relabel_tCount] using optimizedForwardWrapperAdaptive_tCount

/-! Lift an exact T offset through the protected compiler combinators. -/

theorem appendCompiled_tCount_offset {n start d : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (a b : Nat) (hp : compiledTCount p read history + d = a)
    (hq : ∀ h, compiledTCount q read h = b) :
    compiledTCount (appendCompiled p q) read history + d = a + b := by
  rw [appendCompiled_tCount p q read history b hq]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun x ↦ x + b) hp

theorem appendCompiled_tCount_offset_right {n start d : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (a b : Nat) (hp : compiledTCount p read history = a)
    (hq : ∀ h, compiledTCount q read h + d = b) :
    compiledTCount (appendCompiled p q) read history + d = a + b := by
  have hd : d ≤ b := by
    have h := hq (fun _ ↦ false)
    omega
  have hq' : ∀ h, compiledTCount q read h = b - d := by
    intro h
    have := hq h
    omega
  rw [appendCompiled_tCount p q read history (b-d) hq']
  change (p.2.instantiate read history).tCount = a at hp
  rw [hp]
  omega

theorem surroundCircuit_eq (before after : Circuit) (target : AdaptiveCircuit) :
    AdaptiveCircuit.unitary before
        (target.seq (AdaptiveCircuit.unitary after .done)) =
      ((AdaptiveCircuit.unitary before .done).seq target).seq
        (AdaptiveCircuit.unitary after .done) := by
  rw [adaptive_seq_assoc]
  rfl

theorem appendRetaining_tCount_offset {n start d : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (next : (cursor : Nat) → List (Fin cursor) →
      (count : Nat) × Straight n cursor (cursor+count))
    (prior : List (Fin start)) (before : AdaptiveCircuit)
    (after : List Bool → AdaptiveCircuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (hp : compiledTCount p read history + d = before.tCount)
    (hn : ∀ cursor indices h,
      compiledTCount (next cursor indices) read h = (after (indices.map h)).tCount) :
    compiledTCount (appendRetaining p next prior) read history + d =
      (before.seq (after (prior.map history))).tCount := by
  unfold appendRetaining appendCompiled compiledTCount
  rw [castFinish_instantiate]
  rw [append_tCount_prior p.2 _ history read history (after (prior.map history))
    (Nat.le_refl _) (by intro i hi hj; rfl)]
  · change (p.2.instantiate read history).tCount + d = before.tCount at hp
    simp only [adaptive_tCount_seq]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      congrArg (fun x ↦ x + (after (prior.map history)).tCount) hp
  · intro h hagree
    change compiledTCount (next _ _) read h = _
    rw [hn]
    congr 2
    simp only [List.map_map]
    apply List.map_congr_left
    intro i _
    exact hagree i.val i.isLt (Nat.lt_of_lt_of_le i.isLt
      (Nat.le_add_right start p.1))

theorem collectProgram_tCount_offset (n d : Nat)
    (next : (cursor : Nat) → List (Fin cursor) →
      (count : Nat) × Straight n cursor (cursor+count))
    (source : List Bool → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hn : ∀ cursor prior history,
      compiledTCount (next cursor prior) read history + d =
        (source (prior.map history)).tCount)
    (ws : List Wire) (start : Nat) (prior : List (Fin start))
    (history : Fin start → Bool) :
    compiledTCount (collectProgram n next ws start prior) read history + d =
      (measureResetThen ws
        (fun outcomes ↦ source (prior.map history ++ outcomes))).tCount := by
  induction ws generalizing start prior with
  | nil =>
      simpa only [collectProgram, measureResetThen, List.append_nil] using
        hn start prior history
  | cons w ws ih =>
      simp only [collectProgram, compiledTCount, castFinish_instantiate,
        Straight.instantiate, AdaptiveCircuit.tCount, measureResetThen]
      have hf := ih (start+1) (prior.map Fin.castSucc ++ [Fin.last start])
        (Fin.lastCases false history)
      have ht := ih (start+1) (prior.map Fin.castSucc ++ [Fin.last start])
        (Fin.lastCases true history)
      simp only [compiledTCount] at hf ht
      rw [show (prior.map Fin.castSucc ++ [Fin.last start]).map
          (Fin.lastCases false history) = prior.map history ++ [false] by
            simp [List.map_append, List.map_map, Function.comp_def]] at hf
      rw [show (prior.map Fin.castSucc ++ [Fin.last start]).map
          (Fin.lastCases true history) = prior.map history ++ [true] by
            simp [List.map_append, List.map_map, Function.comp_def]] at ht
      simpa only [max_add_add_right, List.singleton_append, List.append_assoc] using
        congrArg₂ max hf ht

theorem surroundCompiled_tCount_offset {n start d : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (target : AdaptiveCircuit) (read : ConstantBit n → Bool)
    (history : Fin start → Bool)
    (hp : compiledTCount p read history + d = target.tCount) :
    compiledTCount (surroundCompiled before after p) read history + d =
      (AdaptiveCircuit.unitary before
        (target.seq (.unitary after .done))).tCount := by
  unfold surroundCompiled
  have htail : compiledTCount
      (appendCompiled p ⟨0, literalProgram after⟩) read history + d =
      target.tCount + ShorECDLP.tCount after := by
    apply appendCompiled_tCount_offset p ⟨0, literalProgram after⟩ read history
      target.tCount (ShorECDLP.tCount after) hp
    intro h
    exact literalProgram_tCount after read h
  unfold prependCompiled
  simp only [compiledTCount, literalProgram_append_tCount,
    AdaptiveCircuit.tCount, adaptive_tCount_seq]
  change ShorECDLP.tCount before +
      compiledTCount (appendCompiled p ⟨0, literalProgram after⟩) read history + d =
    ShorECDLP.tCount before + (target.tCount + ShorECDLP.tCount after)
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun x ↦ ShorECDLP.tCount before + x) htail

def optimizedDivisionProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let eea := optimizedForwardWrapperProgram n start
  let first := appendCompiled eea (multiplyWorkProgram n (start+eea.1))
  appendCompiled first
    (collectProgram n (divisionAfterResetProgram n) (List.range' 580 256)
      (start+first.1) ([] : List (Fin _)))

theorem optimizedDivisionProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedDivisionProgram n start) read history =
      secp256k1InPlaceDivision.run := by
  unfold optimizedDivisionProgram secp256k1InPlaceDivision
  apply appendCompiled_run_eq
  · apply appendCompiled_run_eq
    · exact optimizedForwardWrapperProgram_run n start read history
    · intro h; exact multiplyWorkProgram_run n _ read h
  · intro h
    exact collectProgram_run n (divisionAfterResetProgram n)
      fig15DivisionAfterReset read
      (fun cursor prior h ↦ divisionAfterResetProgram_run n cursor prior read h)
      _ _ ([] : List (Fin _)) h

theorem optimizedDivisionProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedDivisionProgram n start) read history +
        84 * secp256k1ScheduleLength = secp256k1InPlaceDivision.tCount := by
  unfold optimizedDivisionProgram
  let eea := optimizedForwardWrapperProgram n start
  let mul := multiplyWorkProgram n (start+eea.1)
  have hfirst : compiledTCount (appendCompiled eea mul) read history +
      84 * secp256k1ScheduleLength =
      secp256k1MeasuredEEAForwardWrapper.tCount + fig15MultiplyToWork.tCount := by
    apply appendCompiled_tCount_offset eea mul read history
      secp256k1MeasuredEEAForwardWrapper.tCount fig15MultiplyToWork.tCount
    · exact optimizedForwardWrapperProgram_tCount n start read history
    · intro h; exact multiplyWorkProgram_tCount n _ read h
  have htotal := appendCompiled_tCount_offset _ _ read history
    (secp256k1MeasuredEEAForwardWrapper.tCount + fig15MultiplyToWork.tCount)
    (measureResetThen (List.range' 580 256) fig15DivisionAfterReset).tCount hfirst
    (fun h ↦ collectProgram_tCount n (divisionAfterResetProgram n)
      fig15DivisionAfterReset read
      (fun cursor prior h ↦ divisionAfterResetProgram_tCount n cursor prior read h)
      _ _ ([] : List (Fin _)) h)
  rw [secp256k1InPlaceDivision]
  simpa only [adaptive_tCount_seq] using htotal

def optimizedMultiplicationAfterResetProgram (n start : Nat)
    (prior : List (Fin start)) :
    (count : Nat) × Straight n start (start+count) :=
  let eea := optimizedForwardDataBankProgram n start
  appendRetaining (appendCompiled eea (multiplyDataProgram n (start+eea.1)))
    (multiplicationCorrectionProgram n) prior

theorem optimizedMultiplicationAfterResetProgram_run (n start : Nat)
    (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    compiledRun (optimizedMultiplicationAfterResetProgram n start prior) read history =
      (fig15MultiplicationAfterReset (prior.map history)).run := by
  unfold optimizedMultiplicationAfterResetProgram
  have h := appendRetaining_run
    (appendCompiled (optimizedForwardDataBankProgram n start)
      (multiplyDataProgram n _))
    (multiplicationCorrectionProgram n) prior
    (secp256k1MeasuredEEAForwardInDataBank.seq fig15MultiplyToData)
    (fun outcomes ↦
      (AdaptiveCircuit.unitary
        (registerZCorrection (List.range' 580 256) outcomes) .done).seq
        multiplicationCleanupSource)
    read history (by
      apply appendCompiled_run_eq
      · exact optimizedForwardDataBankProgram_run n start read history
      · intro h; exact multiplyDataProgram_run n _ read h)
    (fun cursor indices h ↦
      multiplicationCorrectionProgram_run n cursor indices read h)
  simpa only [fig15MultiplicationAfterReset, multiplicationCleanupSource,
    adaptive_seq_assoc] using h

theorem optimizedMultiplicationAfterResetProgram_tCount (n start : Nat)
    (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    compiledTCount (optimizedMultiplicationAfterResetProgram n start prior) read history +
        84 * secp256k1ScheduleLength =
      (fig15MultiplicationAfterReset (prior.map history)).tCount := by
  unfold optimizedMultiplicationAfterResetProgram
  let eea := optimizedForwardDataBankProgram n start
  let mul := multiplyDataProgram n (start+eea.1)
  have hfirst : compiledTCount (appendCompiled eea mul) read history +
      84 * secp256k1ScheduleLength =
      (secp256k1MeasuredEEAForwardInDataBank.seq fig15MultiplyToData).tCount := by
    rw [adaptive_tCount_seq]
    apply appendCompiled_tCount_offset eea mul read history
      secp256k1MeasuredEEAForwardInDataBank.tCount fig15MultiplyToData.tCount
    · exact optimizedForwardDataBankProgram_tCount n start read history
    · intro h; exact multiplyDataProgram_tCount n _ read h
  have h := appendRetaining_tCount_offset
    (appendCompiled eea mul) (multiplicationCorrectionProgram n) prior
    (secp256k1MeasuredEEAForwardInDataBank.seq fig15MultiplyToData)
    (fun outcomes ↦
      (AdaptiveCircuit.unitary
        (registerZCorrection (List.range' 580 256) outcomes) .done).seq
        multiplicationCleanupSource)
    read history hfirst
    (fun cursor indices h ↦
      multiplicationCorrectionProgram_tCount n cursor indices read h)
  simpa only [fig15MultiplicationAfterReset, multiplicationCleanupSource,
    adaptive_seq_assoc] using h

def optimizedMultiplicationProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let first := multiplyWorkProgram n start
  appendCompiled first
    (collectProgram n (optimizedMultiplicationAfterResetProgram n)
      (List.range' 580 256) (start+first.1) ([] : List (Fin _)))

theorem optimizedMultiplicationProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedMultiplicationProgram n start) read history =
      secp256k1InPlaceMultiplication.run := by
  unfold optimizedMultiplicationProgram secp256k1InPlaceMultiplication
  apply appendCompiled_run_eq
  · exact multiplyWorkProgram_run n start read history
  · intro h
    exact collectProgram_run n (optimizedMultiplicationAfterResetProgram n)
      fig15MultiplicationAfterReset read
      (fun cursor prior h ↦
        optimizedMultiplicationAfterResetProgram_run n cursor prior read h)
      _ _ ([] : List (Fin _)) h

theorem optimizedMultiplicationProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedMultiplicationProgram n start) read history +
        84 * secp256k1ScheduleLength =
      secp256k1InPlaceMultiplication.tCount := by
  unfold optimizedMultiplicationProgram
  let first := multiplyWorkProgram n start
  have htail := collectProgram_tCount_offset n
    (84 * secp256k1ScheduleLength)
    (optimizedMultiplicationAfterResetProgram n) fig15MultiplicationAfterReset read
    (fun cursor prior h ↦
      optimizedMultiplicationAfterResetProgram_tCount n cursor prior read h)
    (List.range' 580 256) (start+first.1) ([] : List (Fin _))
  have hfirst := multiplyWorkProgram_tCount n start read history
  have htotal := appendCompiled_tCount_offset_right first _ read history
    fig15MultiplyToWork.tCount
    (measureResetThen (List.range' 580 256) fig15MultiplicationAfterReset).tCount
    hfirst (fun h ↦ by simpa only [List.map_nil, List.nil_append] using htail h)
  rw [secp256k1InPlaceMultiplication]
  simpa only [adaptive_tCount_seq] using htotal

def optimizedZeroDivisionProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  surroundCompiled fig15ZeroPrepare fig15ZeroRestore
    (optimizedDivisionProgram n start)

theorem optimizedZeroDivisionProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedZeroDivisionProgram n start) read history =
      secp256k1ZeroAllowedDivision.run := by
  unfold optimizedZeroDivisionProgram
  have h := surroundCompiled_run fig15ZeroPrepare fig15ZeroRestore
    (optimizedDivisionProgram n start) secp256k1InPlaceDivision read history
    (optimizedDivisionProgram_run n start read history)
  exact h.trans (congrArg AdaptiveCircuit.run
    (surroundCircuit_eq fig15ZeroPrepare fig15ZeroRestore
      secp256k1InPlaceDivision))

theorem optimizedZeroDivisionProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedZeroDivisionProgram n start) read history +
        84 * secp256k1ScheduleLength = secp256k1ZeroAllowedDivision.tCount := by
  unfold optimizedZeroDivisionProgram
  have h := surroundCompiled_tCount_offset fig15ZeroPrepare fig15ZeroRestore
    (optimizedDivisionProgram n start) secp256k1InPlaceDivision read history
    (optimizedDivisionProgram_tCount n start read history)
  exact h.trans (congrArg AdaptiveCircuit.tCount
    (surroundCircuit_eq fig15ZeroPrepare fig15ZeroRestore
      secp256k1InPlaceDivision))

def optimizedZeroMultiplicationProgram (n start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  surroundCompiled fig15ZeroPrepare fig15ZeroRestore
    (optimizedMultiplicationProgram n start)

theorem optimizedZeroMultiplicationProgram_run (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (optimizedZeroMultiplicationProgram n start) read history =
      secp256k1ZeroAllowedMultiplication.run := by
  unfold optimizedZeroMultiplicationProgram
  have h := surroundCompiled_run fig15ZeroPrepare fig15ZeroRestore
    (optimizedMultiplicationProgram n start) secp256k1InPlaceMultiplication read history
    (optimizedMultiplicationProgram_run n start read history)
  exact h.trans (congrArg AdaptiveCircuit.run
    (surroundCircuit_eq fig15ZeroPrepare fig15ZeroRestore
      secp256k1InPlaceMultiplication))

theorem optimizedZeroMultiplicationProgram_tCount (n start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (optimizedZeroMultiplicationProgram n start) read history +
        84 * secp256k1ScheduleLength =
      secp256k1ZeroAllowedMultiplication.tCount := by
  unfold optimizedZeroMultiplicationProgram
  have h := surroundCompiled_tCount_offset fig15ZeroPrepare fig15ZeroRestore
    (optimizedMultiplicationProgram n start) secp256k1InPlaceMultiplication read history
    (optimizedMultiplicationProgram_tCount n start read history)
  exact h.trans (congrArg AdaptiveCircuit.tCount
    (surroundCircuit_eq fig15ZeroPrepare fig15ZeroRestore
      secp256k1InPlaceMultiplication))

inductive TOffsetForall₂ {n : Nat} (read : ConstantBit n → Bool) :
    List (FixedSegment n) → List AdaptiveCircuit → Nat → Prop
  | nil : TOffsetForall₂ read List.nil List.nil 0
  | cons {p source ps sources tail} (d : Nat)
      (head : ∀ start history,
        compiledTCount (p start) read history + d = source.tCount)
      (rest : TOffsetForall₂ read ps sources tail) :
      TOffsetForall₂ read (List.cons p ps) (List.cons source sources) (d+tail)

theorem sequenceProgram_tCount_offset {n : Nat} (read : ConstantBit n → Bool)
    {ps : List (FixedSegment n)} {sources : List AdaptiveCircuit} {d : Nat}
    (h : TOffsetForall₂ read ps sources d) (start : Nat)
    (history : Fin start → Bool) :
    compiledTCount (sequenceProgram n ps start) read history + d =
      (sequenceCircuit sources).tCount := by
  induction h generalizing start with
  | nil => rfl
  | @cons p source ps sources tail headD head rest ih =>
      unfold sequenceProgram sequenceCircuit
      have ht := ih (start+(p start).1) (fun _ ↦ false)
      have htail : ∀ h,
          compiledTCount (sequenceProgram n ps (start+(p start).1)) read h + tail =
            (sequenceCircuit sources).tCount := ih _
      have hb : tail ≤ (sequenceCircuit sources).tCount := by
        have := ht
        omega
      have hq : ∀ h,
          compiledTCount (sequenceProgram n ps (start+(p start).1)) read h =
            (sequenceCircuit sources).tCount - tail := by
        intro hist
        have := htail hist
        omega
      rw [appendCompiled_tCount _ _ read history
        ((sequenceCircuit sources).tCount-tail) hq]
      simp only [adaptive_tCount_seq]
      have hh := head start history
      change ((p start).2.instantiate read history).tCount + headD =
        source.tCount at hh
      calc
        ((p start).2.instantiate read history).tCount
              + ((sequenceCircuit sources).tCount - tail) + (headD + tail) =
            (((p start).2.instantiate read history).tCount + headD) +
              (((sequenceCircuit sources).tCount - tail) + tail) := by ac_rfl
        _ = source.tCount + (sequenceCircuit sources).tCount := by
          rw [hh, Nat.sub_add_cancel hb]

def optimizedCoordinateSegments : List (FixedSegment 32768) :=
  [fieldLookupAddProgram .negX (List.range' 263 256), signedFieldProgram .negY,
   optimizedZeroDivisionProgram 32768, pointSquareProgram 32768,
   fieldLookupAddProgram .tripleX (List.range' 263 256),
   optimizedZeroMultiplicationProgram 32768,
   xNegateProgram 32768, fieldLookupAddProgram .x (List.range' 263 256),
   signedFieldProgram .negY]

def optimizedCoordinateProgram (start : Nat) :
    (count : Nat) × Straight 32768 start (start+count) :=
  sequenceProgram 32768 optimizedCoordinateSegments start

theorem optimizedCoordinateProgram_run (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (optimizedCoordinateProgram start)
        (readConstant (oddWindowCoefficients w) Q) history =
      (signedLookupCoordinateProgram
        (fun l ↦ fieldValue (windowPoint Q w l) .x)
        (fun l ↦ fieldValue (windowPoint Q w l) .y)).run := by
  unfold optimizedCoordinateProgram
  rw [← coordinateSources_eq]
  apply sequenceProgram_run
  unfold optimizedCoordinateSegments coordinateSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ List.Forall₂.nil))))))))
  · intro cursor h; exact fig14LookupX_compiled w .negX cursor Q hQ h
  · intro cursor h; exact signedFieldProgram_run w .negY cursor Q hQ h
  · intro cursor h; exact optimizedZeroDivisionProgram_run 32768 cursor _ h
  · intro cursor h; exact pointSquareProgram_run 32768 cursor _ h
  · intro cursor h; exact fig14LookupX_compiled w .tripleX cursor Q hQ h
  · intro cursor h; exact optimizedZeroMultiplicationProgram_run 32768 cursor _ h
  · intro cursor h; exact xNegateProgram_run 32768 cursor _ h
  · intro cursor h; exact fig14LookupX_compiled w .x cursor Q hQ h
  · intro cursor h; exact signedFieldProgram_run w .negY cursor Q hQ h

theorem optimizedCoordinateProgram_tCount (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (optimizedCoordinateProgram start)
        (readConstant (oddWindowCoefficients w) Q) history +
        168 * secp256k1ScheduleLength =
      (signedLookupCoordinateProgram
        (fun l ↦ fieldValue (windowPoint Q w l) .x)
        (fun l ↦ fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold optimizedCoordinateProgram
  rw [← coordinateSources_eq]
  have hrel : TOffsetForall₂ (readConstant (oddWindowCoefficients w) Q)
      optimizedCoordinateSegments (coordinateSources Q w)
      (0 + (0 + (84 * secp256k1ScheduleLength + (0 +
        (0 + (84 * secp256k1ScheduleLength + (0 + (0 + (0 + 0))))))))) := by
    unfold optimizedCoordinateSegments coordinateSources
    apply TOffsetForall₂.cons 0
    · intro cursor h
      simpa using fieldLookupAddProgram_tCount_source w .negX _ cursor Q hQ
        (by simp) h
    apply TOffsetForall₂.cons 0
    · intro cursor h; simpa using signedFieldProgram_tCount w .negY cursor Q hQ h
    apply TOffsetForall₂.cons (84 * secp256k1ScheduleLength)
    · intro cursor h; exact optimizedZeroDivisionProgram_tCount 32768 cursor _ h
    apply TOffsetForall₂.cons 0
    · intro cursor h; simpa using pointSquareProgram_tCount 32768 cursor _ h
    apply TOffsetForall₂.cons 0
    · intro cursor h
      simpa using fieldLookupAddProgram_tCount_source w .tripleX _ cursor Q hQ
        (by simp) h
    apply TOffsetForall₂.cons (84 * secp256k1ScheduleLength)
    · intro cursor h
      exact optimizedZeroMultiplicationProgram_tCount 32768 cursor _ h
    apply TOffsetForall₂.cons 0
    · intro cursor h; simpa using xNegateProgram_tCount 32768 cursor _ h
    apply TOffsetForall₂.cons 0
    · intro cursor h
      simpa using fieldLookupAddProgram_tCount_source w .x _ cursor Q hQ
        (by simp) h
    apply TOffsetForall₂.cons 0
    · intro cursor h; simpa using signedFieldProgram_tCount w .negY cursor Q hQ h
    exact TOffsetForall₂.nil
  have h := sequenceProgram_tCount_offset _ hrel start history
  norm_num only at h ⊢
  exact h

def optimizedSharedCoordinateProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  reindexCompiled (windowIndex w) (optimizedCoordinateProgram start)

theorem optimizedSharedCoordinateProgram_run (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (optimizedSharedCoordinateProgram w start)
        (readConstant coefficientAt Q) history =
      (signedLookupCoordinateProgram
        (fun l ↦ fieldValue (windowPoint Q w l) .x)
        (fun l ↦ fieldValue (windowPoint Q w l) .y)).run := by
  unfold optimizedSharedCoordinateProgram reindexCompiled compiledRun
  rw [reindexStraight_instantiate,
    readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact optimizedCoordinateProgram_run w start Q hQ history

theorem optimizedSharedCoordinateProgram_tCount (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (optimizedSharedCoordinateProgram w start)
        (readConstant coefficientAt Q) history +
        168 * secp256k1ScheduleLength =
      (signedLookupCoordinateProgram
        (fun l ↦ fieldValue (windowPoint Q w l) .x)
        (fun l ↦ fieldValue (windowPoint Q w l) .y)).tCount := by
  unfold optimizedSharedCoordinateProgram reindexCompiled compiledTCount
  rw [reindexStraight_instantiate,
    readConstant_reindex _ _ _ Q (coefficientAt_window w)]
  exact optimizedCoordinateProgram_tCount w start Q hQ history

def optimizedIpxWindowSegments (w : OddWindow) : List (FixedSegment 983040) :=
  [optimizedSharedCoordinateProgram w, sharedYNegateProgram w,
    ipxProgram w, sharedYNegateProgram w]

def optimizedIpxWindowCore (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  sequenceProgram 983040 (optimizedIpxWindowSegments w) start

theorem localSharedYNegateProgram_tCount (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedYNegateProgram w start) read history =
      windowYNegate.tCount := by
  simp only [sharedYNegateProgram, reindexCompiled, compiledTCount,
    reindexStraight_instantiate]
  unfold windowYNegate
  exact yNegateProgram_tCount start _ history

theorem optimizedIpxWindowCore_run (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (optimizedIpxWindowCore w start)
        (readConstant coefficientAt Q) history =
      (sequenceCircuit (ipxWindowSources Q w)).run := by
  apply sequenceProgram_run
  unfold optimizedIpxWindowSegments ipxWindowSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact optimizedSharedCoordinateProgram_run w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_run w cursor _ h
  · intro cursor h; exact ipxProgram_run w cursor Q h
  · intro cursor h; exact sharedYNegateProgram_run w cursor _ h

theorem optimizedIpxWindowCore_tCount (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (optimizedIpxWindowCore w start)
        (readConstant coefficientAt Q) history +
        168 * secp256k1ScheduleLength =
      (sequenceCircuit (ipxWindowSources Q w)).tCount := by
  unfold optimizedIpxWindowCore
  have hrel : TOffsetForall₂ (readConstant coefficientAt Q)
      (optimizedIpxWindowSegments w) (ipxWindowSources Q w)
      (168 * secp256k1ScheduleLength + (0 + (0 + (0 + 0)))) := by
    unfold optimizedIpxWindowSegments ipxWindowSources
    apply TOffsetForall₂.cons (168 * secp256k1ScheduleLength)
    · intro cursor h
      exact optimizedSharedCoordinateProgram_tCount w cursor Q hQ h
    apply TOffsetForall₂.cons 0
    · intro cursor h; simpa using localSharedYNegateProgram_tCount w cursor _ h
    apply TOffsetForall₂.cons 0
    · intro cursor h; simpa using ipxProgram_tCount w cursor Q h
    apply TOffsetForall₂.cons 0
    · intro cursor h; simpa using localSharedYNegateProgram_tCount w cursor _ h
    exact TOffsetForall₂.nil
  simpa only [Nat.add_zero] using
    sequenceProgram_tCount_offset _ hrel start history

def optimizedIpxWindowPrepared (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress)
    (optimizedIpxWindowCore w start)

theorem optimizedIpxWindowPrepared_run (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (optimizedIpxWindowPrepared w start)
        (readConstant coefficientAt Q) history =
      (ipxWindowPreparedSource Q w).run := by
  exact surroundCompiled_run _ _ _ _ _ _
    (optimizedIpxWindowCore_run w start Q hQ history)

theorem optimizedIpxWindowPrepared_tCount (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (optimizedIpxWindowPrepared w start)
        (readConstant coefficientAt Q) history +
        168 * secp256k1ScheduleLength =
      (ipxWindowPreparedSource Q w).tCount := by
  exact surroundCompiled_tCount_offset _ _ _ _ _ _
    (optimizedIpxWindowCore_tCount w start Q hQ history)

def optimizedActualIpxWindow (w : OddWindow) : OuterWindow 983040 :=
  closedWindow (relabelStraight (windowAddressPerm 855 (by decide))
    (optimizedIpxWindowPrepared w 0).2)

theorem optimizedActualIpxWindow_run (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    (((optimizedActualIpxWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).run =
      ((ipxWindowPreparedSource Q w).relabel
        (windowAddressPerm 855 (by decide))).run := by
  simp only [optimizedActualIpxWindow, closedWindow_run,
    relabelStraight_instantiate, AdaptiveCircuit.run_relabel]
  exact congrArg (List.map
    (InstrumentBranch.relabel (windowAddressPerm 855 (by decide))))
    (optimizedIpxWindowPrepared_run w 0 Q hQ Fin.elim0)

theorem optimizedActualIpxWindow_tCount (w : OddWindow) (start : Nat)
    (Q : Point) (hQ : order • Q = 0) (history : Fin start → Bool) :
    (((optimizedActualIpxWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).tCount +
        168 * secp256k1ScheduleLength =
      (ipxWindowPreparedSource Q w).tCount := by
  simp only [optimizedActualIpxWindow, closedWindow_run,
    relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
  change compiledTCount (optimizedIpxWindowPrepared w 0)
    (readConstant coefficientAt Q) Fin.elim0 +
      168 * secp256k1ScheduleLength = _
  exact optimizedIpxWindowPrepared_tCount w 0 Q hQ Fin.elim0

def optimizedIpxLeftWindows : List (OuterWindow 983040) :=
  actualFirstWindow :: List.ofFn
    (fun k : Fin 15 ↦ optimizedActualIpxWindow (.left ⟨14-k.val, by omega⟩))

def optimizedIpxRightWindows : List (OuterWindow 983040) :=
  List.ofFn
    (fun k : Fin 13 ↦ optimizedActualIpxWindow (.right ⟨12-k.val, by omega⟩))

theorem optimizedIpxLeftWindows_length : optimizedIpxLeftWindows.length = 16 := by
  simp [optimizedIpxLeftWindows]

theorem optimizedIpxRightWindows_length : optimizedIpxRightWindows.length = 13 := by
  simp [optimizedIpxRightWindows]

def optimizedIpxOuterPlan : OuterPlan 983040 :=
  standardOuterPlan
    ⟨optimizedIpxLeftWindows.toArray, by simp [optimizedIpxLeftWindows_length]⟩
    ⟨optimizedIpxRightWindows.toArray, by simp [optimizedIpxRightWindows_length]⟩
    resetWires

end ShorECDLP.Paper2607_13816.ChallengeMigration
