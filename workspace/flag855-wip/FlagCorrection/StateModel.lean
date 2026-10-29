import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.EndpointLogic

namespace ShorECDLP.FlagCorrection

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def stateFlagModel (st : BasisState) : FlagModel :=
  ⟨fun i => st (accumulatorPort i), fun k => st k.val⟩

noncomputable def stateEndpointWords {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (st : BasisState) : Fin 8 → FlagWord := fun j =>
  normalizedEndpointWords coeffs Q (rows (batchWindowTree.routeLabel st)) j

def FlagDomain (st : BasisState) : Prop := FlagReady st ∧ st 836 = true

theorem accumulatorPort_ne_836 (i : Fin 513) : 836 ≠ accumulatorPort i := by
  decide +kernel +revert

theorem accumulatorPort_ne_flag (i : Fin 513) (flag : Fin 4) :
    accumulatorPort i ≠ flag.val := by
  decide +kernel +revert

theorem accumulatorPort_le_838 (i : Fin 513) : accumulatorPort i ≤ 838 := by
  decide +kernel +revert

theorem flag_ne_836 (flag : Fin 4) : 836 ≠ flag.val := by
  decide +kernel +revert

theorem wordIsZero_stateFlagModel (st : BasisState) :
    wordIsZero (stateFlagModel st).data = accZero st := by
  apply Bool.eq_iff_iff.mpr
  simp only [wordIsZero, decide_eq_true_eq, accZero_eq_true_iff]
  constructor
  · intro h i
    have := congrFun h i
    simpa [stateFlagModel, zeroWord] using this
  · intro h
    funext i
    simpa [stateFlagModel, zeroWord] using h i

theorem flagOpState_path {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagReady st) (w : Wire) (hw : w ∈ pointLookupPath) :
    flagOpState read rows op st w = st w := by
  cases op with
  | query column control =>
      exact flagQuery_frame_path read rows column control hv st hs.1 w hw
  | test flag =>
      rw [flagOpState, splitZeroTest_run flag.val flag.isLt st hs.2.1 hs.2.2, upd_other]
      intro he
      subst w
      simp only [pointLookupPath, List.mem_range'] at hw
      obtain ⟨i, hi, he⟩ := hw
      omega

theorem flagOpState_root {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagReady st) :
    flagOpState read rows op st 836 = st 836 := by
  cases op with
  | query column control =>
      apply flagQuery_frame read rows column control hv st hs.1
      intro i he
      exact accumulatorPort_ne_836 i he
  | test flag =>
      rw [flagOpState, splitZeroTest_run flag.val flag.isLt st hs.2.1 hs.2.2, upd_other]
      exact flag_ne_836 flag

theorem flagOpState_domain {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagDomain st) :
    FlagDomain (flagOpState read rows op st) := by
  exact ⟨flagOpState_ready read rows op hv st hs.1,
    (flagOpState_root read rows op hv st hs.1).trans hs.2⟩

theorem flagOpState_route {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagReady st) :
    batchWindowTree.routeLabel (flagOpState read rows op st) =
      batchWindowTree.routeLabel st := by
  apply UnaryActionTree.routeLabel_congr
  intro w hw
  cases op with
  | query column control =>
      apply flagQuery_frame read rows column control hv st hs.1 w
      have hd : w ∈ batchWindowTree.indexWires.dedup := List.mem_dedup.mpr hw
      unfold batchWindowTree at hd
      rw [tableAddressTree_index pointLookupAddress 0 1 (by decide)] at hd
      have hlo : 839 ≤ w := by
        simp only [pointLookupAddress, List.mem_range'] at hd
        obtain ⟨i, hi, rfl⟩ := hd
        exact Nat.le_add_right 839 (1 * i)
      intro i he
      have hu := accumulatorPort_le_838 i
      have hlt : accumulatorPort i < 839 := lt_of_le_of_lt hu (by decide)
      rw [← he] at hlt
      exact (Nat.not_lt_of_ge hlo) hlt
  | test flag =>
      rw [flagOpState, splitZeroTest_run flag.val flag.isLt st hs.2.1 hs.2.2, upd_other]
      intro he
      have hf := flag.isLt
      have hd : w ∈ batchWindowTree.indexWires.dedup := List.mem_dedup.mpr hw
      unfold batchWindowTree at hd
      rw [tableAddressTree_index pointLookupAddress 0 1 (by decide)] at hd
      simp only [pointLookupAddress, List.mem_range'] at hd
      obtain ⟨i, hi, hwi⟩ := hd
      have hlo : 839 ≤ w := by rw [hwi]; exact Nat.le_add_right 839 (1 * i)
      exact (Nat.ne_of_gt (flag.isLt.trans ((by decide : 4 < 839).trans_le hlo))) he

theorem flagOpState_frame {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagReady st) (w : Wire) (hw : 4 ≤ w)
    (hout : ∀ i : Fin 513, w ≠ accumulatorPort i) :
    flagOpState read rows op st w = st w := by
  cases op with
  | query column control => exact flagQuery_frame read rows column control hv st hs.1 w hout
  | test flag =>
      rw [flagOpState, splitZeroTest_run flag.val flag.isLt st hs.2.1 hs.2.2, upd_other]
      intro he
      rw [he] at hw
      exact (Nat.not_le_of_lt flag.isLt) hw

theorem runFlagOps_frame {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (ops : List FlagOp) (hv : ∀ op ∈ ops, op.Valid)
    (st : BasisState) (hs : FlagDomain st) (w : Wire) (hw : 4 ≤ w)
    (hout : ∀ i : Fin 513, w ≠ accumulatorPort i) :
    runFlagOps read rows ops st w = st w := by
  induction ops generalizing st with
  | nil => rfl
  | cons op ops ih =>
      have hop : op.Valid := hv op (by simp)
      let t := flagOpState read rows op st
      have ht := flagOpState_domain read rows op hop st hs
      rw [runFlagOps, ih (fun x hx => hv x (by simp [hx])) t ht]
      exact flagOpState_frame read rows op hop st hs.1 w hw hout

theorem flagCorrectionState_frame {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (st : BasisState) (hs : FlagDomain st)
    (w : Wire) (hw : 4 ≤ w) (hout : ∀ i : Fin 513, w ≠ accumulatorPort i) :
    flagCorrectionState read rows st w = st w :=
  runFlagOps_frame read rows flagSchedule flagSchedule_valid st hs w hw hout

theorem stateEndpointWords_op {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagReady st) :
    stateEndpointWords coeffs Q rows (flagOpState (readConstant coeffs Q) rows op st) =
      stateEndpointWords coeffs Q rows st := by
  unfold stateEndpointWords
  rw [flagOpState_route (readConstant coeffs Q) rows op hv st hs]

theorem flagOpState_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (op : FlagOp) (hv : op.Valid)
    (st : BasisState) (hs : FlagDomain st) :
    stateFlagModel (flagOpState (readConstant coeffs Q) rows op st) =
      flagModelStep (stateEndpointWords coeffs Q rows st) (stateFlagModel st) op := by
  cases op with
  | query column control =>
      apply FlagModel.ext
      · funext i
        simp only [stateFlagModel, flagOpState]
        rw [flagQuery_word coeffs Q rows column control hv st hs.1.1 i]
        by_cases hr : control = 836
        · subst control
          simp [flagModelStep, stateEndpointWords, flagWordXor, hs.2]
        · have hc : control < 4 := hv.resolve_right hr
          cases hsc : st control <;>
            simp [flagModelStep, stateEndpointWords, flagWordXor, hr, hc, hsc]
      · funext k
        simp only [stateFlagModel, flagOpState]
        rw [flagQuery_frame_low (readConstant coeffs Q) rows column control hv st hs.1.1
          (w := k.val) (k.isLt.trans (by decide))]
        rfl
  | test flag =>
      rw [flagOpState, splitZeroTest_run flag.val flag.isLt st hs.1.2.1 hs.1.2.2]
      apply FlagModel.ext
      · funext i
        simp [stateFlagModel, flagModelStep, upd, accumulatorPort_ne_flag i flag]
      · funext k
        change (st[flag.val ↦ xor (st flag.val) (accZero st)]) k.val =
          if k = flag then xor (st flag.val) (wordIsZero (stateFlagModel st).data)
          else st k.val
        rw [← wordIsZero_stateFlagModel st]
        by_cases hk : k = flag
        · subst k
          simp [upd]
        · have hv : k.val ≠ flag.val := fun h => hk (Fin.ext h)
          simp [upd, hk, hv]

theorem runFlagOps_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (ops : List FlagOp) (hv : ∀ op ∈ ops, op.Valid)
    (st : BasisState) (hs : FlagDomain st) :
    stateFlagModel (runFlagOps (readConstant coeffs Q) rows ops st) =
      ops.foldl (flagModelStep (stateEndpointWords coeffs Q rows st)) (stateFlagModel st) := by
  induction ops generalizing st with
  | nil => rfl
  | cons op ops ih =>
      have hop : op.Valid := hv op (by simp)
      let t := flagOpState (readConstant coeffs Q) rows op st
      have ht : FlagDomain t := flagOpState_domain _ _ op hop st hs
      have hi := ih (fun x hx => hv x (by simp [hx])) t ht
      have hw := stateEndpointWords_op coeffs Q rows op hop st hs.1
      rw [runFlagOps, hi, hw, flagOpState_model coeffs Q rows op hop st hs]
      rfl

theorem flagCorrectionState_model {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (st : BasisState) (hs : FlagDomain st) :
    stateFlagModel (flagCorrectionState (readConstant coeffs Q) rows st) =
      runFlagModel (stateEndpointWords coeffs Q rows st) (stateFlagModel st) := by
  exact runFlagOps_model coeffs Q rows flagSchedule flagSchedule_valid st hs

end ShorECDLP.FlagCorrection
