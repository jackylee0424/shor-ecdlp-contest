import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredStep

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

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
    unfold optimizedMeasuredStepSegments optimizedMeasuredStepSources sources
    dsimp only
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
      (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_
        (List.Forall₂.cons ?_ List.Forall₂.nil))))))
    · intro cursor hist; exact literalCompiled_tCount _ read hist
    · intro cursor hist; exact remainderBlockProgram_tCount n cursor _ 256 _ read hist
    · intro cursor hist; exact literalCompiled_tCount _ read hist
    · intro cursor hist
      rw [optimizedCoefficientProgram_tCount_formula n cursor T read hist]
    · intro cursor hist; exact literalCompiled_tCount _ read hist
    · intro cursor hist; exact phaseProgram_tCount n cursor _ _ read hist
    · intro cursor hist; exact hProgram_tCount n cursor _ 256 T read hist
  unfold optimizedMeasuredStepProgram
  rw [sequenceProgram_tCount n (optimizedMeasuredStepSegments n T) sources read hs start history]
  rw [← measuredStepSources_eq indexedStepProductionRegisters 256 T]
  simp only [optimizedMeasuredStepSources, measuredStepSources, sequenceCircuit,
    adaptive_tCount_seq]
  have hc := optimizedCoefficientAdaptive_tCount T
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration
