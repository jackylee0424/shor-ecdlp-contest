import ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution
import ShorECDLP.Submission.«2607_13816».Challenge.BatchPlacement
import ShorECDLP.Submission.«2607_13816».Challenge.PlacedBatch
import ShorECDLP.Submission.«2607_13816».Challenge.Relabel
import ShorECDLP.Submission.Entrant.Streaming.Dirty.DirtyMCX

namespace ShorECDLP.FlagCorrection

set_option maxRecDepth 100000

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- Swap the first temporary batch word with the live 513-bit accumulator. -/
def flagPlacementFn (w : Wire) : Wire :=
  if 1024 ≤ w ∧ w < 1280 then 263 + (w - 1024)
  else if 1280 ≤ w ∧ w < 1536 then 580 + (w - 1280)
  else if w = 1536 then 838
  else if 263 ≤ w ∧ w < 519 then 1024 + (w - 263)
  else if 580 ≤ w ∧ w < 836 then 1280 + (w - 580)
  else if w = 838 then 1536 else w

theorem flagPlacementFn_involutive : Function.Involutive flagPlacementFn := by
  intro w
  generalize hv : flagPlacementFn w = v
  unfold flagPlacementFn at hv
  split_ifs at hv <;> subst v <;> unfold flagPlacementFn <;> split_ifs <;>
    dsimp only [Wire] at * <;> omega

def flagPlacement : Wire ≃ Wire :=
  ⟨flagPlacementFn, flagPlacementFn, flagPlacementFn_involutive,
    flagPlacementFn_involutive⟩

def queryPlacement (control : Wire) : Wire ≃ Wire :=
  flagPlacement.trans (Equiv.swap 836 control)

theorem flagPlacement_data (i : Fin 513) :
    flagPlacement (batchWord 1024 0 i) = accumulatorPort i := by
  change flagPlacementFn (1024 + i.val) = _
  unfold flagPlacementFn accumulatorPort
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem flagPlacement_low (w : Wire) (hw : w < 263 ∨ 519 ≤ w ∧ w < 580 ∨
    836 ≤ w ∧ w < 838 ∨ 839 ≤ w ∧ w < 1024) : flagPlacement w = w := by
  change flagPlacementFn w = w
  unfold flagPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

def oneColumn (column : Fin 8) : List (Fin 8 × Fin 5) := [(column, 0)]

noncomputable def flagQueryUnitary {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire) : Circuit :=
  (unaryActionUnitary .inc
    (fun l q => batchLeafCircuit read (rows l) 1024 q (oneColumn column))
    batchWindowTree 836 pointLookupPath).map (Gate.relabel (queryPlacement control))

noncomputable def flagQuerySource {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire) : AdaptiveCircuit :=
  (unaryAction .inc
    (fun l q => batchLeafCircuit read (rows l) 1024 q (oneColumn column))
    batchWindowTree 836 pointLookupPath).relabel (queryPlacement control)

theorem oneColumn_nodup (column : Fin 8) :
    ((oneColumn column).map Prod.snd).Nodup := by simp [oneColumn]

noncomputable def flagQueryState {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire) (st : BasisState) : BasisState :=
  relabelBasis (queryPlacement control)
    (Classical.run (unaryActionUnitary .inc
      (fun l q => batchLeafCircuit read (rows l) 1024 q (oneColumn column))
      batchWindowTree 836 pointLookupPath) (relabelBasis (queryPlacement control).symm st))

private theorem coherentRelabelState {program : AdaptiveCircuit} {c : Circuit}
    {P : BasisState → Prop}
    (h : CoherentlyImplementsOn program (Quantum.run c) P) (hc : HPFree c)
    (e : Wire ≃ Wire) :
    CoherentlyImplementsOn (program.relabel e)
      (Finsupp.lmapDomain ℂ ℂ
        (fun st => relabelBasis e (Classical.run c (relabelBasis e.symm st))))
      (fun st => P (relabelBasis e.symm st)) := by
  apply (h.relabel e).congrIdeal
  intro st hs
  simp only [LinearMap.comp_apply, relabelState_ket]
  rw [run_ket_agrees_classical c _ hc, relabelState_ket]
  simp only [ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem flagQuery_coherent {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire) :
    CoherentlyImplementsOn (flagQuerySource read rows column control)
      (Finsupp.lmapDomain ℂ ℂ (flagQueryState read rows column control))
      (fun st => Clean pointLookupPath (relabelBasis (queryPlacement control).symm st)) := by
  have h := batchQuery_coherent read rows 1024 batchWindowTree 836 pointLookupPath
    (oneColumn column) (oneColumn_nodup column) batchWindowTree_layout
    (fun w hw => Or.inl (batchWindowTree_below w hw))
  apply coherentRelabelState h
  apply unaryActionUnitary_HPFree
  intro l q
  unfold batchLeafCircuit
  rw [Classical.hpFree_append]
  exact ⟨tableXorGates_HPFree _ _, tableXorGates_HPFree _ _⟩

theorem queryPlacement_index (control w : Wire) (hc : control < 4 ∨ control = 836)
    (hw : w ∈ batchWindowTree.indexWires) : queryPlacement control w = w := by
  have ha : w ∈ pointLookupAddress := by
    have hd : w ∈ batchWindowTree.indexWires.dedup := List.mem_dedup.mpr hw
    unfold batchWindowTree at hd
    rw [tableAddressTree_index pointLookupAddress 0 1 (by decide)] at hd
    exact hd
  have hb : 839 ≤ w ∧ w < 854 := by
    simp only [pointLookupAddress, List.mem_range'] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    dsimp only [Wire]
    omega
  unfold queryPlacement
  rw [Equiv.trans_apply, flagPlacement_low w
    (Or.inr (Or.inr (Or.inr ⟨hb.1, hb.2.trans (by decide)⟩)))]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem queryPlacement_path (control w : Wire) (hc : control < 4 ∨ control = 836)
    (hw : w ∈ pointLookupPath) : queryPlacement control w = w := by
  have hb : 519 ≤ w ∧ w < 534 := by
    simp only [pointLookupPath, List.mem_range'] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    dsimp only [Wire]
    omega
  unfold queryPlacement
  rw [Equiv.trans_apply, flagPlacement_low w
    (Or.inr (Or.inl ⟨hb.1, hb.2.trans (by decide)⟩))]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem flagQuery_route (control : Wire) (hc : control < 4 ∨ control = 836) (st : BasisState) :
    batchWindowTree.routeLabel (relabelBasis (queryPlacement control).symm st) =
      batchWindowTree.routeLabel st := by
  apply UnaryActionTree.routeLabel_congr
  intro w hw
  change st (queryPlacement control w) = st w
  rw [queryPlacement_index control w hc hw]

theorem flagQuery_control (st : BasisState) (control : Wire) :
    relabelBasis (queryPlacement control).symm st 836 = st control := by
  change st (queryPlacement control 836) = st control
  unfold queryPlacement
  rw [Equiv.trans_apply, flagPlacement_low 836
    (Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩)))]
  simp

theorem flagQuery_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire)
    (hc : control < 4 ∨ control = 836)
    (st : BasisState) (hclean : Clean pointLookupPath st) (i : Fin 513) :
    flagQueryState (readConstant coeffs Q) rows column control st (accumulatorPort i) =
      xor (st (accumulatorPort i))
        (st control && normalizedEndpointWords coeffs Q
          (rows (batchWindowTree.routeLabel st)) column i) := by
  let s := relabelBasis (queryPlacement control).symm st
  have hs : Clean pointLookupPath s := by
    intro w hw
    change st (queryPlacement control w) = false
    rw [queryPlacement_path control w hc hw]
    exact hclean w hw
  have hword := batchQuery_word coeffs Q rows 1024 batchWindowTree 836 pointLookupPath
    (oneColumn column) (oneColumn_nodup column) batchWindowTree_layout
    (fun w hw => Or.inl (batchWindowTree_below w hw))
    s hs (column, 0) (by simp [oneColumn]) i
  have hdata : queryPlacement control (batchWord 1024 0 i) = accumulatorPort i := by
    unfold queryPlacement
    rw [Equiv.trans_apply, flagPlacement_data]
    simp only [Equiv.swap_apply_def]
    unfold accumulatorPort
    split_ifs <;> dsimp only [Wire] at * <;> omega
  change Classical.run _ s ((queryPlacement control).symm (accumulatorPort i)) = _
  rw [← hdata, Equiv.symm_apply_apply]
  simpa only [Function.comp_apply, s, flagQuery_control st control,
    flagQuery_route control hc st] using hword

end ShorECDLP.FlagCorrection
