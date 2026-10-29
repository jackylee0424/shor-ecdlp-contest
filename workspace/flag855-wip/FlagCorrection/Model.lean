import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Program

namespace ShorECDLP.FlagCorrection

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def FlagReady (st : BasisState) : Prop :=
  Clean pointLookupPath st ∧ Clean halfScratch st ∧ st halfFlag = false

def FlagOp.Valid : FlagOp → Prop
  | .query _ control => control < 4 ∨ control = 836
  | .test _ => True

theorem flagSchedule_valid : ∀ op ∈ flagSchedule, op.Valid := by
  simp [flagSchedule, flagDetectSchedule, flagUpdateSchedule, flagClearSchedule,
    FlagOp.Valid, q]

noncomputable def flagOpState {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (st : BasisState) : BasisState :=
  match op with
  | .query column control => flagQueryState read rows column control st
  | .test flag => Classical.run (splitZeroTest flag.val) st

noncomputable def runFlagOps {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) : List FlagOp → BasisState → BasisState
  | [], st => st
  | op :: ops, st => runFlagOps read rows ops (flagOpState read rows op st)

noncomputable def flagCorrectionState {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) : BasisState → BasisState :=
  runFlagOps read rows flagSchedule

private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs, hc, hm⟩ := h
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (hp s hs)), hm⟩

theorem flagQuery_pullback_clean (control : Wire) (hc : control < 4 ∨ control = 836)
    (st : BasisState) (hs : Clean pointLookupPath st) :
    Clean pointLookupPath (relabelBasis (queryPlacement control).symm st) := by
  intro w hw
  change st (queryPlacement control w) = false
  rw [queryPlacement_path control w hc hw]
  exact hs w hw

theorem flagQueryState_ready {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire)
    (hc : control < 4 ∨ control = 836) (st : BasisState) (hs : FlagReady st) :
    FlagReady (flagQueryState read rows column control st) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rw [flagQuery_frame_path read rows column control hc st hs.1 w hw]
    exact hs.1 w hw
  · intro w hw
    have hlow : w < 263 := by
      simp only [halfScratch, List.mem_range'] at hw
      obtain ⟨i, hi, rfl⟩ := hw
      have h : 4 + i < 4 + 255 := Nat.add_lt_add_left hi 4
      norm_num at h ⊢
      exact Nat.lt_trans h (by norm_num)
    rw [flagQuery_frame_low read rows column control hc st hs.1 (w := w) hlow]
    exact hs.2.1 w hw
  · rw [flagQuery_frame_low read rows column control hc st hs.1 halfFlag (by
      unfold halfFlag
      decide)]
    exact hs.2.2

theorem splitZeroTest_ready (flag : Fin 4) (st : BasisState) (hs : FlagReady st) :
    FlagReady (Classical.run (splitZeroTest flag.val) st) := by
  rw [splitZeroTest_run flag.val flag.isLt st hs.2.1 hs.2.2]
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    rw [upd_other]
    · exact hs.1 w hw
    · intro he
      subst w
      simp only [pointLookupPath, List.mem_range'] at hw
      omega
  · intro w hw
    rw [upd_other]
    · exact hs.2.1 w hw
    · intro he
      subst w
      simp only [halfScratch, List.mem_range'] at hw
      omega
  · rw [upd_other]
    · exact hs.2.2
    · unfold halfFlag
      dsimp only [Wire]
      omega

theorem flagOpState_ready {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagReady st) :
    FlagReady (flagOpState read rows op st) := by
  cases op with
  | query column control => exact flagQueryState_ready read rows column control hv st hs
  | test flag => exact splitZeroTest_ready flag st hs

theorem flagOp_coherent {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid) :
    CoherentlyImplementsOn (flagOpSource read rows op)
      (Finsupp.lmapDomain ℂ ℂ (flagOpState read rows op)) FlagReady := by
  cases op with
  | query column control =>
      exact restrictCoherent (flagQuery_coherent read rows column control)
        (fun st hs => flagQuery_pullback_clean control hv st hs.1)
  | test flag =>
      have h := CoherentlyImplementsOn.unitary (splitZeroTest flag.val) FlagReady
      apply h.congrIdeal
      intro st hs
      rw [run_ket_agrees_classical _ _ (splitZeroTest_HPFree flag.val)]
      simp only [flagOpState, ket, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

private theorem composeStateCoherent {a b : AdaptiveCircuit} {f g : BasisState → BasisState}
    {P R : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) P)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) R)
    (hf : ∀ s, P s → R (f s)) :
    CoherentlyImplementsOn (a.seq b)
      (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) P := by
  have h := ha.seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket R (f s) (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply, ket]

private theorem doneStateCoherent (P : BasisState → Prop) :
    CoherentlyImplementsOn AdaptiveCircuit.done
      (Finsupp.lmapDomain ℂ ℂ (fun s : BasisState => s)) P := by
  have hd : CoherentlyImplementsOn AdaptiveCircuit.done LinearMap.id P := by
    refine ⟨[1], ?_, by simp⟩
    simp only [AdaptiveCircuit.run]
    apply List.Forall₂.cons
    · intro s hs
      simp
    · exact .nil
  apply hd.congrIdeal
  intro s hs
  simp [ket]

theorem runFlagOps_coherent {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (ops : List FlagOp) (hv : ∀ op ∈ ops, op.Valid) :
    CoherentlyImplementsOn (sequenceCircuit (ops.map (flagOpSource read rows)))
      (Finsupp.lmapDomain ℂ ℂ (runFlagOps read rows ops)) FlagReady := by
  induction ops with
  | nil =>
      simpa [sequenceCircuit, runFlagOps] using doneStateCoherent FlagReady
  | cons op ops ih =>
      have hop := flagOp_coherent read rows op (hv op (by simp))
      have htail := ih (fun x hx => hv x (by simp [hx]))
      have h := composeStateCoherent hop htail
        (fun st hs => flagOpState_ready read rows op (hv op (by simp)) st hs)
      simpa only [List.map_cons, sequenceCircuit, runFlagOps] using h

theorem flagCorrectionSource_coherent {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) :
    CoherentlyImplementsOn (flagCorrectionSource read rows)
      (Finsupp.lmapDomain ℂ ℂ (flagCorrectionState read rows)) FlagReady := by
  exact runFlagOps_coherent read rows flagSchedule flagSchedule_valid

end ShorECDLP.FlagCorrection
