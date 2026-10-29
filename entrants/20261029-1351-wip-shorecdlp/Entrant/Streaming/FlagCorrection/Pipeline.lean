import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Window
import ShorECDLP.Submission.Entrant.Streaming.Challenge.ActualWindow

namespace ShorECDLP.FlagCorrection

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

private theorem flag_point_bank_bound (w : Wire) (hw : w ∈ pointLogicalWires) : w < 839 := by
  simp only [pointLogicalWires, pointCorrectionX, pointCorrectionYInf, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

private theorem flag_relabel_pointWrite (start : Nat) (hs : 855 ≤ start)
    (P : Point) (s : BasisState) :
    relabelBasis (windowAddressPerm start hs)
      (pointWrite P (relabelBasis (windowAddressPerm start hs).symm s)) = pointWrite P s := by
  have hsym : (windowAddressPerm start hs).symm = windowAddressPerm start hs := rfl
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · have he := windowAddressPerm_core start hs w (flag_point_bank_bound w hw)
    simp [relabelBasis, hsym, he, pointWrite, hw]
  · have hn : (windowAddressPerm start hs).symm w ∉ pointLogicalWires := by
      intro h
      have he := windowAddressPerm_core start hs _ (flag_point_bank_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp [relabelBasis, pointWrite, hw, hn]

private theorem flag_relabel_coordinates (start : Nat) (hs : 855 ≤ start)
    (s : BasisState) :
    pointStateCoordinates (relabelBasis (windowAddressPerm start hs).symm s) =
      pointStateCoordinates s := by
  have he (bits : List Wire) (hb : ∀ w ∈ bits, w < 839) :
      wireValues bits (relabelBasis (windowAddressPerm start hs).symm s) =
        wireValues bits s := by
    apply List.map_congr_left
    intro w hw
    simp only [relabelBasis, Equiv.symm_symm, windowAddressPerm_core start hs w (hb w hw)]
  have hx := he (List.range' 263 256) (by
    intro w hw
    simp only [List.mem_range'_1] at hw
    dsimp only [Wire] at *
    omega)
  have hy := he (List.range' 580 256) (by
    intro w hw
    simp only [List.mem_range'_1] at hw
    dsimp only [Wire] at *
    omega)
  simp only [pointStateCoordinates, hx, hy, relabelBasis, Equiv.symm_symm,
    windowAddressPerm_core start hs 838 (by decide)]

noncomputable def flagPreparedState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  batchPrepareState (flagBatchedWindowState Q w (batchPrepareState s))

theorem flagBatchedWindowState_valid (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (flagBatchedWindowState Q w s) := by
  obtain ⟨hs, P, hP⟩ := hs
  rw [flagBatchedWindowState_correct Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs, _, pointWrite_coordinates _ s⟩

theorem flagPreparedState_correct (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    flagPreparedState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w
          (tableAddressValue pointLookupAddress (batchPrepareState s))
        else -windowPoint Q w
          (tableAddressValue pointLookupAddress (batchPrepareState s))) s := by
  unfold flagPreparedState
  rw [flagBatchedWindowState_correct Q hQ hn w _ (batchPrepareState_ready s hs) P
    ((batchPrepareState_coordinates s).trans hP), batchPrepareState_pointWrite,
    batchPrepareState_involution, batchPrepareState_frame s 854 (by decide)]

def flagBatchedWindowPrepared (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start + count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (flagBatchedWindowCore w start)

noncomputable def flagBatchedWindowPreparedSource (Q : Point) (w : OddWindow) :
    AdaptiveCircuit :=
  (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
    ((sequenceCircuit (flagBatchedWindowSources Q w)).seq
      (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))

theorem flagBatchedWindowPrepared_run (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (flagBatchedWindowPrepared w start) (readConstant coefficientAt Q) history =
      (flagBatchedWindowPreparedSource Q w).run := by
  exact surroundCompiled_run _ _ _ _ _ _
    (flagBatchedWindowCore_run w start Q hQ history)

attribute [local irreducible] batchPrepareState flagBatchedWindowState

theorem flagBatchedWindowPreparedSource_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) :
    CoherentlyImplementsOn (flagBatchedWindowPreparedSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (flagPreparedState Q w)) BatchedWindowValid := by
  have hc := composeCoherent (flagBatchedWindowSources_coherent Q hQ hn w)
    batchPrepare_coherent (flagBatchedWindowState_valid Q hQ hn w)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (flagBatchedWindowState Q w s))
    batchPrepare_coherent hc batchPrepareState_valid
  exact h

def flagActualBatchedWindow (w : OddWindow) : OuterWindow 983040 :=
  closedWindow (relabelStraight (windowAddressPerm 855 (by decide))
    (flagBatchedWindowPrepared w 0).2)

theorem flagActualBatchedWindow_run (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    (((flagActualBatchedWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).run =
      ((flagBatchedWindowPreparedSource Q w).relabel
        (windowAddressPerm 855 (by decide))).run := by
  simp only [flagActualBatchedWindow, closedWindow_run, relabelStraight_instantiate,
    AdaptiveCircuit.run_relabel]
  exact congrArg (List.map (InstrumentBranch.relabel (windowAddressPerm 855 (by decide))))
    (flagBatchedWindowPrepared_run w 0 Q hQ Fin.elim0)

noncomputable def flagActualBatchedWindowState (Q : Point) (w : OddWindow)
    (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (flagPreparedState Q w
      (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

theorem flagActualBatchedWindow_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn (((flagActualBatchedWindow w).program start).instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (flagActualBatchedWindowState Q w))
      BatchedWindowValid := by
  have h := (flagBatchedWindowPreparedSource_coherent Q hQ hn w).relabel
    (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn
      ((flagBatchedWindowPreparedSource Q w).relabel
        (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (flagPreparedState Q w)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm)))
      BatchedWindowValid := by
    obtain ⟨cs, hc, hm⟩ := h
    exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (actualWindow_pullback_valid s hs)), hm⟩
  have he : CoherentlyImplementsOn
      ((flagBatchedWindowPreparedSource Q w).relabel
        (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (flagActualBatchedWindowState Q w))
      BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [flagActualBatchedWindowState, LinearMap.comp_apply, relabelState, ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [flagActualBatchedWindow_run w start Q hQ history]
  exact he

theorem flagActualBatchedWindowState_correct (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    flagActualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis
            (windowAddressPerm 855 (by decide)).symm s)))
        else -windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis
            (windowAddressPerm 855 (by decide)).symm s)))) s := by
  unfold flagActualBatchedWindowState
  rw [flagPreparedState_correct Q hQ hn w _ (actualWindow_pullback_ready s hs) P
    ((flag_relabel_coordinates 855 (by decide) s).trans hP), flag_relabel_pointWrite]
  have he : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854 = s 870 := by
    simp only [relabelBasis, Equiv.symm_symm]
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [he]

theorem flagActualBatchedWindowState_selected (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    flagActualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
        else -windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  rw [flagActualBatchedWindowState_correct Q hQ hn w s hs P hP,
    actualWindow_selected_address s hs]

theorem flagActualBatchedWindowState_valid (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (flagActualBatchedWindowState Q w s) := by
  obtain ⟨hs, P, hP⟩ := hs
  rw [flagActualBatchedWindowState_selected Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs, _, pointWrite_coordinates _ s⟩

theorem flagActualBatchedWindowState_frame (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s)
    (v : Wire) (hv : v ∉ pointLogicalWires) :
    flagActualBatchedWindowState Q w s v = s v := by
  obtain ⟨hs, P, hP⟩ := hs
  rw [flagActualBatchedWindowState_selected Q hQ hn w s hs P hP]
  simp [pointWrite, hv]

def flagActualLeftWindows : List (OuterWindow 983040) :=
  actualFirstWindow :: List.ofFn
    (fun k : Fin 15 => flagActualBatchedWindow (.left ⟨14 - k.val, by omega⟩))

def flagActualRightWindows : List (OuterWindow 983040) :=
  List.ofFn (fun k : Fin 13 => flagActualBatchedWindow (.right ⟨12 - k.val, by omega⟩))

theorem flagActualLeftWindows_length : flagActualLeftWindows.length = 16 := by
  simp [flagActualLeftWindows]

theorem flagActualRightWindows_length : flagActualRightWindows.length = 13 := by
  simp [flagActualRightWindows]

/-- Only the original 855-wire core is reset between streaming rounds. -/
def flagBatchedResetWires : List Wire := resetWires

theorem flagBatchedResetWires_length : flagBatchedResetWires.length = 854 := by
  simp [flagBatchedResetWires, resetWires_length]

def flagBatchedOuterPlan : OuterPlan 983040 :=
  standardOuterPlan
    ⟨flagActualLeftWindows.toArray, by simp [flagActualLeftWindows_length]⟩
    ⟨flagActualRightWindows.toArray, by simp [flagActualRightWindows_length]⟩
    flagBatchedResetWires

end ShorECDLP.FlagCorrection
