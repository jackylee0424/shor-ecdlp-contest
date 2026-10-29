import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation

/-!
Construction and proofs from VerifiedQC/ShorECDLP,
lamport/challenge-final-certificate @ b46e337 (Apache-2.0).
The round count is reduced from 56 to 26 using the upstream per-round
0.163 acceptance bound. The entry and decoder share streamingRounds.
Packaged into existing tracked files for the official source policy;
workspace/port_upstream.py and workspace/package_streaming.py reproduce it.
-/

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.BatchBoundary -/
section Port_BatchBoundary

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge

def batchWorkspace : List Wire := List.range' 1024 2565 ++ List.range' 4102 512
def BatchedPointReady (s : BasisState) : Prop := PointLookupValid s ∧ Clean batchWorkspace s

theorem batchWorkspace_outside (w : Wire) (hw : w ∈ batchWorkspace) : w ∉ pointLogicalWires := by
  simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false]
  dsimp only [Wire] at *
  omega

theorem batchPlacement_aux (w : Wire) (hw : w ∈ 836::pointLookupPath) : batchPlacement w=w := by
  change batchPlacementFn w=w
  simp only [pointLookupPath,List.mem_cons,List.mem_range'_1] at hw
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem batchedPointReady_batch (s : BasisState) (hs : BatchedPointReady s) :
    BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro w hw
    change s (batchPlacement w)=false
    rw [batchPlacement_aux w (List.mem_cons_of_mem _ hw)]
    apply hs.1.1.1 w
    simp only [pointLookupPath,List.mem_range'_1] at hw
    simp only [List.mem_append,List.mem_range'_1]
    omega
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    change s (batchPlacement (1024+3079+i.val))=false
    rw [batchPlacement_high _ (by dsimp only [Wire]; omega)]
    apply hs.2
    simp only [batchWorkspace,List.mem_append,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  · change s (batchPlacement 4102)=false
    rw [batchPlacement_high _ (by decide)]
    exact hs.2 _ (by simp [batchWorkspace])
  · change s (batchPlacement 836)=true
    rw [batchPlacement_aux _ (by simp)]
    exact hs.1.2

theorem batchedPointReady_words (s : BasisState) (hs : BatchedPointReady s) :
    ∀ j : Fin 6, j ≠ 5 → (relabelBasis batchPlacement.symm s) ∘ batchWord 1024 j = fun _ => false := by
  intro j hj
  funext i
  change s (batchPlacement (batchWord 1024 j i))=false
  have hlo : 1024 ≤ batchWord 1024 j i := by dsimp [batchWord,Wire]; omega
  have hhi : batchWord 1024 j i < 3589 := by
    have hjv : j.val ≠ 5 := by intro he; apply hj; exact Fin.ext he
    dsimp [batchWord]
    dsimp only [Wire]
    omega
  rw [batchPlacement_endpoints _ hlo hhi]
  exact hs.2 _ (by simp only [batchWorkspace,List.mem_append,List.mem_range'_1]; dsimp only [Wire] at *; omega)

theorem windowYNegateState_batchedReady (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (windowYNegateState s) := by
  have hf := (windowYNegateState_correct s hs.1.1).2
  refine ⟨⟨windowYNegateState_ready s hs.1.1,?_⟩,?_⟩
  · rw [hf 836 (by decide)]
    exact hs.1.2
  · intro w hw
    rw [hf w (by
      intro hy
      exact batchWorkspace_outside w hw (List.mem_append_right _ (List.mem_append_left _ hy)))]
    exact hs.2 w hw
theorem signedLookupCoordinateState_batchedReady (x y : Nat → Nat) (s : BasisState)
    (hs : BatchedPointReady s) : BatchedPointReady (signedLookupCoordinateState x y s) := by
  refine ⟨signedLookupCoordinateState_ready x y s hs.1,?_⟩
  intro w hw
  have hout := batchWorkspace_outside w hw
  rw [signedLookupCoordinateState_frame x y s hs.1 w
    (fun hx => hout (List.mem_append_left _ hx))
    (fun hy => hout (List.mem_append_right _ (List.mem_append_left _ hy)))]
  exact hs.2 w hw

theorem batchPlacement_address (w : Wire) (hw : w ∈ pointLookupAddress) : batchPlacement w=w := by
  change batchPlacementFn w=w
  simp only [pointLookupAddress,List.mem_range'_1] at hw
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

private theorem port_BatchBoundary_address_frame (bits : List Wire) (s t : BasisState)
    (h : ∀ w ∈ bits, s w=t w) : tableAddressValue bits s=tableAddressValue bits t := by
  induction bits with
  | nil => rfl
  | cons w ws ih =>
    simp only [tableAddressValue,h w (by simp),ih (fun w hw => h w (by simp [hw]))]

theorem batchWindowTree_route (s : BasisState) :
    batchWindowTree.routeLabel (relabelBasis batchPlacement.symm s) = tableAddressValue pointLookupAddress s := by
  rw [batchWindowTree,tableAddressTree_route,zero_add,one_mul]
  apply port_BatchBoundary_address_frame
  intro w hw
  change s (batchPlacement w)=s w
  rw [batchPlacement_address w hw]

theorem windowYNegateState_address (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    tableAddressValue pointLookupAddress (windowYNegateState s)=tableAddressValue pointLookupAddress s := by
  apply port_BatchBoundary_address_frame
  intro w hw
  apply (windowYNegateState_correct s hs).2 w
  simp only [pointLookupAddress,List.mem_range'_1] at hw
  simp only [List.mem_range'_1]
  omega

theorem pointWrite_batchedReady (P : Point) (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (pointWrite P s) := by
  refine ⟨⟨pointWrite_valid P s hs.1.1,?_⟩,?_⟩
  · rw [pointWrite_frame P s 836 (by decide +kernel)]
    exact hs.1.2
  · intro w hw
    rw [pointWrite_frame P s w (batchWorkspace_outside w hw)]
    exact hs.2 w hw

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_BatchBoundary

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.BatchedWindowState -/
section Port_BatchedWindowState

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
noncomputable def signedBatchState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  windowYNegateState (placedBatchState Q w (windowYNegateState s))

theorem pointWrite_frame_eq (P : Point) (s t : BasisState)
    (h : ∀ w, w ∉ pointLogicalWires → s w=t w) : pointWrite P s=pointWrite P t := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hw]
  · simp only [pointWrite,if_neg hw,h w hw]

theorem signedBatchState_pointWrite (Q : Point) (w : OddWindow) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s)
    (hb : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm (windowYNegateState s)))
    (hz : ∀ j : Fin 6, j ≠ 5 →
      (relabelBasis batchPlacement.symm (windowYNegateState s)) ∘ batchWord 1024 j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    signedBatchState Q w s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  have he := placedBatchState_pointWrite Q w _ hb hz ht hC hr P' hd
  have hsign : placedBatchState Q w (windowYNegateState s) 854 = s 854 :=
    (placedBatchState_frame Q w _ hb hz 854 (by decide +kernel)).trans
      ((windowYNegateState_correct s hs).2 854 (by decide +kernel))
  have hv := placedBatchState_ready Q w _ hb hz ht hC hr P' hd
  have hc := placedBatchState_coordinates Q w _ hb hz ht hC hr P' hd
  unfold signedBatchState
  rw [windowYNegateState_pointWrite (P' + .some hC) _ hv hc,hsign,he,pointWrite_overwrite]
  have hpoint : (if s 854 then P' + .some hC else -(P' + .some hC)) =
      P + if s 854 then .some hC else -(.some hC) := by
    cases hsg : s 854 <;> simp [P',hsg,add_comm]
  rw [hpoint]
  apply pointWrite_frame_eq
  intro v hv
  apply (windowYNegateState_correct s hs).2 v
  intro hy
  exact hv (List.mem_append_right _ (List.mem_append_left _ hy))
noncomputable def batchedWindowState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  signedBatchState Q w (signedLookupCoordinateState
    (fun a => fieldValue (windowPoint Q w a) .x) (fun a => fieldValue (windowPoint Q w a) .y) s)

theorem batchedWindowState_finite (Q : Point) (hQ : order • Q=0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : windowPoint Q w (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState Q w s = pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have hn := windowYNegateState_batchedReady t ht
  have ha : tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854=s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState t))))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    unfold batchWindowRows
    rw [coefficientAt_window,oddWindowCoefficients_point w _ Q hQ]
    have hb : tableAddressValue pointLookupAddress s < 32768 := tableAddressValue_lt pointLookupAddress s
    simpa only [Nat.mod_eq_of_lt hb] using hr
  have hx : xs (tableAddressValue pointLookupAddress s)=x.val := by simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s)=y.val := by simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s=(if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t=fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  have he := signedBatchState_pointWrite Q w t ht.1.1 (batchedPointReady_batch _ hn)
    (batchedPointReady_words _ hn) hC hr' P hd
  change signedBatchState Q w t= _
  rw [he,hz]
  apply pointWrite_frame_eq
  intro v hv
  exact signedLookupCoordinateState_frame xs ys s hs.1 v
    (fun hx => hv (List.mem_append_left _ hx))
    (fun hy => hv (List.mem_append_right _ (List.mem_append_left _ hy)))
theorem windowPoint_ne_zero (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) (a : Nat) :
    windowPoint Q w a ≠ 0 := by
  cases w with
  | left j => exact oddWindowPoint_ne_zero G G_ne_zero generator_nsmul_eq_zero j.val a
  | right j => exact oddWindowPoint_ne_zero Q hn hQ j.val a

theorem batchedWindowState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    batchedWindowState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress s)
        else -windowPoint Q w (tableAddressValue pointLookupAddress s)) s := by
  cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
  | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
  | some hC => exact batchedWindowState_finite Q hQ w s hs hC he P hP

theorem signedBatchState_middle_ready (Q : Point) (w : OddWindow) (s : BasisState)
    (hs : Secp256k1ZeroAllowedInputValid s)
    (hb : BatchReady 1024 836 pointLookupPath (relabelBasis batchPlacement.symm (windowYNegateState s)))
    (hz : ∀ j : Fin 6, j ≠ 5 →
      (relabelBasis batchPlacement.symm (windowYNegateState s)) ∘ batchWord 1024 j = fun _ => false)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC)
    (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (placedBatchState Q w (windowYNegateState s)) := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have hd : pointStateCoordinates (windowYNegateState s) = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  exact placedBatchState_ready Q w _ hb hz ht hC hr P' hd

def SignedBatchReady (Q : Point) (w : OddWindow) (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y),
    constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState s))))) = .some hC ∧
    ∃ P : Point, pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_BatchedWindowState

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.BatchedWindowCoherent -/
section Port_BatchedWindowCoherent

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩
private theorem port_BatchedWindowCoherent_restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

theorem composeCoherent {a b : AdaptiveCircuit} {f g : BasisState → BasisState}
    {P R : BasisState → Prop}
    (ha : CoherentlyImplementsOn a (Finsupp.lmapDomain ℂ ℂ f) P)
    (hb : CoherentlyImplementsOn b (Finsupp.lmapDomain ℂ ℂ g) R)
    (hf : ∀ s, P s → R (f s)) :
    CoherentlyImplementsOn (a.seq b) (Finsupp.lmapDomain ℂ ℂ (fun s => g (f s))) P := by
  have h := ha.seq hb (by
    intro s hs
    simpa [ket] using supportedOn_ket R (f s) (hf s hs))
  apply h.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket]

noncomputable def signedBatchSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (windowYNegate.seq (placedBatchSource Q w)).seq windowYNegate

theorem signedBatchSource_coherent (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (signedBatchSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (signedBatchState Q w)) (SignedBatchReady Q w) := by
  have hneg : CoherentlyImplementsOn windowYNegate (Finsupp.lmapDomain ℂ ℂ windowYNegateState)
      (SignedBatchReady Q w) := port_BatchedWindowCoherent_restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (placedBatchSource_state Q w) (fun s hs =>
    batchedPointReady_batch _ (windowYNegateState_batchedReady s hs.1))
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨hr,x,y,hC,hrow,P,hdata⟩ := hs
    have hn := windowYNegateState_batchedReady s hr
    exact signedBatchState_middle_ready Q w s hr.1.1 (batchedPointReady_batch _ hn)
      (batchedPointReady_words _ hn) hC hrow P hdata)
  exact hlast
theorem batchedWindow_coordinate_ready (Q : Point) (hQ : order • Q=0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hr : windowPoint Q w (tableAddressValue pointLookupAddress s)=.some hC)
    (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    SignedBatchReady Q w (signedLookupCoordinateState
      (fun a => fieldValue (windowPoint Q w a) .x) (fun a => fieldValue (windowPoint Q w a) .y) s) := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have hn := windowYNegateState_batchedReady t ht
  have ha : tableAddressValue pointLookupAddress t=tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854=s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm (windowYNegateState t))))) = .some hC := by
    rw [batchWindowTree_route,windowYNegateState_address t ht.1.1,ha]
    unfold batchWindowRows
    rw [coefficientAt_window,oddWindowCoefficients_point w _ Q hQ]
    have hb : tableAddressValue pointLookupAddress s < 32768 := tableAddressValue_lt pointLookupAddress s
    simpa only [Nat.mod_eq_of_lt hb] using hr
  have hx : xs (tableAddressValue pointLookupAddress s)=x.val := by simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s)=y.val := by simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s=(if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t=fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  exact ⟨ht,x,y,hC,hr',P,hd⟩

def BatchedWindowValid (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ P : Point, pointStateCoordinates s=fig14PointEncoding P

theorem batchedWindowSources_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (sequenceCircuit (batchedWindowSources Q w))
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState Q w)) BatchedWindowValid := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  have hfirst : CoherentlyImplementsOn (signedLookupCoordinateProgram xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    port_BatchedWindowCoherent_restrictCoherent (signedLookupCoordinateProgram_coherent xs ys) (fun s hs => hs.1.1)
  have h := composeCoherent hfirst (signedBatchSource_coherent Q w) (by
    intro s hs
    obtain ⟨hs,P,hP⟩ := hs
    cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
    | some hC => exact batchedWindow_coordinate_ready Q hQ w s hs hC he P hP)
  simpa only [batchedWindowSources,sequenceCircuit,signedBatchSource,adaptive_seq_assoc,adaptive_seq_done,
    batchedWindowState,xs,ys] using h
theorem batchedWindowCore_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((batchedWindowCore w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (batchedWindowState Q w)) BatchedWindowValid := by
  have h := batchedWindowSources_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := batchedWindowCore_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_BatchedWindowCoherent

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.PreparedBatch -/
section Port_PreparedBatch

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
def batchPrepareState : BasisState → BasisState := signedAddressState 836 854 pointLookupAddress

theorem batchPrepareState_frame (s : BasisState) (w : Wire) (hw : w ∉ pointLookupAddress) :
    batchPrepareState s w=s w := signedAddressState_frame 836 854 pointLookupAddress s w hw

private theorem port_PreparedBatch_address_outside_point (w : Wire) (hw : w ∈ pointLogicalWires) : w ∉ pointLookupAddress := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,List.mem_range'_1,
    List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [pointLookupAddress,List.mem_range'_1]
  dsimp only [Wire] at *
  omega

private theorem port_PreparedBatch_prepare_word (s : BasisState) (bits : List Wire)
    (h : ∀ w ∈ bits, w ∉ pointLookupAddress) : wireValues bits (batchPrepareState s)=wireValues bits s := by
  apply List.map_congr_left
  intro w hw
  exact batchPrepareState_frame s w (h w hw)

theorem batchPrepareState_ready (s : BasisState) (hs : BatchedPointReady s) : BatchedPointReady (batchPrepareState s) := by
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩
  · intro w hw
    rw [batchPrepareState_frame s w (by
      simp only [List.mem_append,List.mem_range'_1] at hw
      simp only [pointLookupAddress,List.mem_range'_1]
      omega)]
    exact hs.1.1.1 w hw
  · rw [batchPrepareState_frame s 837 (by decide)]
    exact hs.1.1.2.1
  · rw [port_PreparedBatch_prepare_word s (List.range' 263 256) (fun w hw => port_PreparedBatch_address_outside_point w (List.mem_append_left _ hw))]
    exact hs.1.1.2.2.1
  · rw [port_PreparedBatch_prepare_word s (List.range' 580 256) (fun w hw => port_PreparedBatch_address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]
    exact hs.1.1.2.2.2
  · rw [batchPrepareState_frame s 836 (by decide)]
    exact hs.1.2
  · intro w hw
    rw [batchPrepareState_frame s w (by
      simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
      simp only [pointLookupAddress,List.mem_range'_1]
      omega)]
    exact hs.2 w hw

theorem batchPrepareState_coordinates (s : BasisState) : pointStateCoordinates (batchPrepareState s)=pointStateCoordinates s := by
  unfold pointStateCoordinates
  rw [batchPrepareState_frame s 838 (by decide),
    port_PreparedBatch_prepare_word s (List.range' 263 256) (fun w hw => port_PreparedBatch_address_outside_point w (List.mem_append_left _ hw)),
    port_PreparedBatch_prepare_word s (List.range' 580 256) (fun w hw => port_PreparedBatch_address_outside_point w (List.mem_append_right _ (List.mem_append_left _ hw)))]

theorem batchPrepareState_pointWrite (P : Point) (s : BasisState) :
    batchPrepareState (pointWrite P s)=pointWrite P (batchPrepareState s) := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · rw [batchPrepareState_frame _ w (port_PreparedBatch_address_outside_point w hw)]
    simp only [pointWrite,if_pos hw]
  · rw [pointWrite_frame _ _ w hw]
    unfold batchPrepareState signedAddressState tableXorState
    rw [pointWrite_frame P s 854 (by decide +kernel),pointWrite_frame P s 836 (by decide +kernel),pointWrite_frame P s w hw]

theorem batchPrepareState_involution (s : BasisState) : batchPrepareState (batchPrepareState s)=s :=
  signedAddressState_involution 836 854 pointLookupAddress (by decide) (by decide) s
theorem batchPrepareState_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (batchPrepareState s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨batchPrepareState_ready s hs,P,(batchPrepareState_coordinates s).trans hP⟩

theorem batchedWindowState_valid (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (batchedWindowState Q w s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [batchedWindowState_correct Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

noncomputable def preparedBatchState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  batchPrepareState (batchedWindowState Q w (batchPrepareState s))

theorem preparedBatchState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    preparedBatchState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress (batchPrepareState s))
        else -windowPoint Q w (tableAddressValue pointLookupAddress (batchPrepareState s))) s := by
  unfold preparedBatchState
  rw [batchedWindowState_correct Q hQ hn w _ (batchPrepareState_ready s hs) P
    ((batchPrepareState_coordinates s).trans hP),batchPrepareState_pointWrite,
    batchPrepareState_involution,batchPrepareState_frame s 854 (by decide)]

theorem batchPrepare_coherent : CoherentlyImplementsOn
    (.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done)
    (Finsupp.lmapDomain ℂ ℂ batchPrepareState) BatchedWindowValid := by
  have h := CoherentlyImplementsOn.unitary (signedAddressCircuit 836 854 pointLookupAddress) BatchedWindowValid
  apply h.congrIdeal
  intro s hs
  simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,ket,batchPrepareState] using
    signedAddressCircuit_ket 836 854 pointLookupAddress (by decide) (by decide) (by decide) s

attribute [local irreducible] batchPrepareState batchedWindowState

theorem batchedWindowPreparedSource_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow) :
    CoherentlyImplementsOn (batchedWindowPreparedSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have hc := composeCoherent (batchedWindowSources_coherent Q hQ hn w) batchPrepare_coherent
    (batchedWindowState_valid Q hQ hn w)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (batchedWindowState Q w s))
    batchPrepare_coherent hc batchPrepareState_valid
  exact h

theorem batchedWindowPrepared_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((batchedWindowPrepared w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)) BatchedWindowValid := by
  have h := batchedWindowPreparedSource_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := batchedWindowPrepared_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_PreparedBatch

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowPhysical -/
section Port_WindowPhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem literalProgram_wellFormed {n s : Nat} (gs : Circuit) (h : CircuitWellFormed gs) :
    (literalProgram (n:=n) (s:=s) gs).WellFormed := by
  apply gateProgram_wellFormed
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  exact h v hv

theorem appendCompiled_wellFormed {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : p.2.WellFormed) (hq : q.2.WellFormed) : (appendCompiled p q).2.WellFormed := by
  simpa only [appendCompiled,castFinish_wellFormed] using straight_append_wellFormed p.2 q.2 hp hq

theorem prependCompiled_wellFormed {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hg : CircuitWellFormed gs) (hp : p.2.WellFormed) : (prependCompiled gs p).2.WellFormed :=
  straight_append_wellFormed _ _ (literalProgram_wellFormed gs hg) hp

theorem surroundCompiled_wellFormed {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hb : CircuitWellFormed before) (ha : CircuitWellFormed after) (hp : p.2.WellFormed) :
    (surroundCompiled before after p).2.WellFormed :=
  prependCompiled_wellFormed _ _ hb (appendCompiled_wellFormed _ _ hp (literalProgram_wellFormed after ha))

theorem sequenceProgram_wellFormed (n : Nat) (ps : List (FixedSegment n))
    (hp : ∀ p∈ps,∀ start,(p start).2.WellFormed) (start : Nat) :
    (sequenceProgram n ps start).2.WellFormed := by
  induction ps generalizing start with
  | nil => trivial
  | cons p ps ih =>
    exact appendCompiled_wellFormed _ _ (hp p (by simp) start)
      (ih (fun q hq => hp q (by simp [hq])) _)

theorem reindexStraight_wellFormed {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    (reindexStraight f p).WellFormed ↔ p.WellFormed := by
  have hg (g : TemplateGate n) : (reindexGate f g).WellFormed ↔ g.WellFormed := by
    cases g <;> rfl
  induction p with
  | done => rfl
  | gate g p ih => simp only [reindexStraight,Straight.WellFormed,hg,ih]
  | recordGate i v g p ih => simp only [reindexStraight,Straight.WellFormed,ih]
  | measure w p ih => exact ih

theorem reindexCompiled_wellFormed {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    (reindexCompiled f p).2.WellFormed ↔ p.2.WellFormed :=
  reindexStraight_wellFormed f p.2

theorem registerCorrectionProgram_wellFormed {n s e : Nat} (ws : List Wire)
    (indices : List (Fin s)) (next : Straight n s e) (hn : next.WellFormed) :
    (registerCorrectionProgram ws indices next).WellFormed := by
  induction ws generalizing indices with
  | nil => exact hn
  | cons w ws ih =>
    cases indices with
    | nil => exact hn
    | cons i is =>
      exact recordGates_wellFormed i (pauliZ w) _ (by simp [pauliZ,CircuitWellFormed,Gate.WellFormed]) (ih is)

theorem deferredCorrectionProgram_wellFormed (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (hc : CircuitWellFormed cleanup)
    (hcs : ∀ cell ∈ cells, CircuitWellFormed cell.1) (start : Nat) (prior : List (Fin start)) :
    (deferredCorrectionProgram n targets cleanup cells start prior).WellFormed := by
  induction cells generalizing start with
  | nil =>
    exact registerCorrectionProgram_wellFormed _ _ _
      (straight_append_wellFormed _ _ (literalProgram_wellFormed cleanup hc)
        (registerCorrectionProgram_wellFormed _ _ _ trivial))
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp only [deferredCorrectionProgram,castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalProgram_wellFormed gs (hcs (gs,w) (by simp)))
      (ih (fun c h => hcs c (by simp [h])) _ _)

theorem deferredCorrectionCircuit_physical (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (outcomes : List Bool)
    (h : (deferredCorrectionCircuit targets cleanup cells outcomes).WellFormed) :
    CircuitWellFormed cleanup ∧ ∀ cell∈cells,CircuitWellFormed cell.1 := by
  induction cells generalizing outcomes with
  | nil =>
    have hc := h.1
    simp only [CircuitWellFormed,List.forall_mem_append] at hc
    exact ⟨hc.1.2,by simp⟩
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    obtain ⟨hc,ht⟩ := ih (outcomes++[false]) h.2.1
    exact ⟨hc,by intro c hm; rcases List.mem_cons.mp hm with rfl|hm; exact h.1; exact ht c hm⟩

theorem deferredCorrectionProgram_wellFormed_of_source (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (outcomes : List Bool)
    (h : (deferredCorrectionCircuit targets cleanup cells outcomes).WellFormed)
    (start : Nat) (prior : List (Fin start)) :
    (deferredCorrectionProgram n targets cleanup cells start prior).WellFormed := by
  obtain ⟨hc,ht⟩ := deferredCorrectionCircuit_physical targets cleanup cells outcomes h
  exact deferredCorrectionProgram_wellFormed n targets cleanup cells hc ht start prior

theorem gidneyNontrivialProgram_wellFormed (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length = ds.length+1) (hk : ks.length=as.length)
    (hnz : (k::ks).all (fun b => !b)=false)
    (h : (controlledGidneyAddConst (a::as) (d::ds) (k::ks) q carry spare ancilla).WellFormed) :
    (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).WellFormed := by
  have hh : CircuitWellFormed (gidneyAddCarryCell q carry spare ancilla a d k) ∧
      (deferredCorrectionCircuit (d::ds) (gidneyAddCleanup (a::as) (d::ds) (k::ks) q carry)
        (gidneyCarryCells q spare carry ancilla as ds ks) List.nil).WellFormed := by
    rw [← gidneyCarryCells_source q spare carry ancilla as ds ks _ _ List.nil hd hk]
    cases as with
    | nil => simp at hd
    | cons b bs => simpa only [controlledGidneyAddConst,hnz,Bool.false_eq_true,if_false,
        AdaptiveCircuit.WellFormed] using h
  exact straight_append_wellFormed _ _ (literalProgram_wellFormed _ hh.1)
    (deferredCorrectionProgram_wellFormed_of_source n _ _ _ List.nil hh.2 start List.nil)

theorem gidneyProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1) (hk : constant.length=input.length)
    (h : (controlledGidneyAddConst input dirty constant q carry spare ancilla).WellFormed) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.WellFormed := by
  let WF : ((count : Nat) × Straight n start (start+count)) → Prop := fun p => p.2.WellFormed
  change WF (gidneyProgram n start input dirty constant q carry spare ancilla)
  unfold gidneyProgram
  split
  · trivial
  · rename_i hz
    have hnz : constant.all (fun k => !k)=false := Bool.eq_false_iff.mpr hz
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst as
          have hks : ks=[] := List.eq_nil_of_length_eq_zero (by simpa using hk)
          subst ks
          dsimp only [WF]
          apply literalProgram_wellFormed
          have hh := h
          unfold controlledGidneyAddConst at hh
          simp only [hnz,Bool.false_eq_true,if_false,AdaptiveCircuit.WellFormed] at hh
          exact hh.1
        | cons d ds =>
          cases as with
          | nil => simp at hd
          | cons b bs =>
            dsimp only [WF]
            exact gidneyNontrivialProgram_wellFormed n start a d q carry spare ancilla (b::bs) ds k ks
              (by simpa using hd) (by simpa using hk) hnz h

theorem gidneyProgram_wellFormed (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1) (hk : constant.length=input.length)
    (hnd : ([q,carry,spare,ancilla]++input++dirty).Nodup) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.WellFormed :=
  gidneyProgram_wellFormed_of_source n start input dirty constant q carry spare ancilla hd hk
    (controlledGidneyAddConst_wellFormed input dirty constant q carry spare ancilla hk.symm hd hnd)

theorem compareCarryCells_wellFormed (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (targets : List Wire)
    (cleanup : Circuit) (outcomes : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (gidneyCompareTail q current spare ancilla flag
      (fun bs => registerZCorrection targets bs ++ cleanup ++ registerZCorrection targets bs)
      outcomes input dirty constant).WellFormed) :
    (deferredCorrectionCircuit targets cleanup
      (compareCarryCells q current spare ancilla flag input dirty constant) outcomes).WellFormed := by
  induction input generalizing current spare dirty constant outcomes with
  | nil =>
    have hd' : dirty=[] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant=[] := List.eq_nil_of_length_eq_zero hk
    subst dirty
    subst constant
    exact ⟨by simp [CircuitWellFormed],h⟩
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact ⟨h.1,ih spare current dirty constant (outcomes++[false]) (by simpa using hd)
          (by simpa using hk) h.2.1,
          ih spare current dirty constant (outcomes++[true]) (by simpa using hd)
          (by simpa using hk) h.2.2⟩

theorem compareCarryProgram_wellFormed_of_source (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (controlledGidneyCompareCarry (a::input) (d::dirty) (k::constant) q carry spare ancilla flag).WellFormed) :
    (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).WellFormed := by
  have hh := compareCarryCells_wellFormed q spare carry ancilla flag input dirty constant (d::dirty)
    (controlledConstCarryXor (a::input) (d::dirty) (k::constant) q carry) List.nil hd hk h.2
  exact straight_append_wellFormed _ _ (literalProgram_wellFormed _ h.1)
    (deferredCorrectionProgram_wellFormed_of_source n _ _ _ List.nil hh start List.nil)

theorem compareCoreProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (controlledGidneyCompareCarry input dirty constant q carry spare ancilla flag).WellFormed) :
    (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2.WellFormed := by
  cases input with
  | nil => trivial
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact compareCarryProgram_wellFormed_of_source n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk) h

theorem compareGEProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (h : (controlledGidneyCompareGE input dirty threshold q carry spare ancilla flag).WellFormed) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.WellFormed := by
  let WF : ((count : Nat) × Straight n start (start+count)) → Prop := fun p => p.2.WellFormed
  change WF (compareGEProgram n start input dirty threshold q carry spare ancilla flag)
  unfold compareGEProgram
  split
  · rename_i hz
    exact literalProgram_wellFormed _ (by simpa only [controlledGidneyCompareGE,if_pos hz,
      AdaptiveCircuit.WellFormed,and_true] using h)
  · rename_i hz
    split
    · trivial
    · rename_i hh
      apply compareCoreProgram_wellFormed_of_source _ _ _ _ _ _ _ _ _ _ hd (by simp)
      simpa only [controlledGidneyCompareGE,if_neg hz,if_neg hh] using h

theorem compareGEProgram_wellFormed (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (hnd : ([q,carry,spare,ancilla,flag]++input++dirty).Nodup) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.WellFormed :=
  compareGEProgram_wellFormed_of_source n start input dirty threshold q carry spare ancilla flag hd
    (controlledGidneyCompareGE_wellFormed input dirty threshold q carry spare ancilla flag hd hnd)

theorem modularNegateProgram_wellFormed (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (modularNegateProgram n start target dirty modulus q c r t f).2.WellFormed := by
  have hl := constantModular_layout target dirty q c r t f hnd
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  have hq : q∉target := by
    intro hh
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 q (by simp) q hh rfl
  unfold modularNegateProgram
  apply appendCompiled_wellFormed
  · exact compareGEProgram_wellFormed n start target dirty 1 q c r t f hd hnd
  · apply prependCompiled_wellFormed
    · intro gate hg
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
      exact fun he => hq (he ▸ hw)
    · apply appendCompiled_wellFormed
      · exact gidneyProgram_wellFormed _ _ _ _ _ q c r t htake (by simp) hl.1
      · apply appendCompiled_wellFormed
        · exact gidneyProgram_wellFormed _ _ _ _ _ f c r t htake hk.symm hl.2.1
        · exact compareGEProgram_wellFormed _ _ target dirty 1 q c r t f hd hnd

theorem negativeNegateProgram_wellFormed (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (negativeNegateProgram n start target dirty modulus q c r t f).2.WellFormed :=
  prependCompiled_wellFormed _ _ (by simp [CircuitWellFormed,Gate.WellFormed])
    (appendCompiled_wellFormed _ _ (modularNegateProgram_wellFormed n start target dirty modulus q c r t f hk hd hn hnd)
      (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])))

theorem yNegateProgram_wellFormed (start : Nat) : (yNegateProgram start).2.WellFormed :=
  negativeNegateProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp [constantBits_length])
    (by simp) (by simp) (by decide +kernel)

theorem sharedYNegateProgram_wellFormed (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).2.WellFormed :=
  (reindexCompiled_wellFormed (windowIndex w) (yNegateProgram start)).mpr (yNegateProgram_wellFormed start)

attribute [local irreducible] modularNegateProgram

theorem xNegateProgram_wellFormed (n start : Nat) : (xNegateProgram n start).2.WellFormed := by
  unfold xNegateProgram
  apply modularNegateProgram_wellFormed n start (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558 (by simp [constantBits_length]) (by simp) (by simp)
  rw [List.nodup_append,List.nodup_append]
  refine ⟨⟨by decide,by exact List.nodup_range',?_⟩,by exact List.nodup_range',?_⟩
  · intro a ha b hb he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [List.mem_range'_1] at hb
    dsimp only [Wire] at *
    omega
  · intro a ha b hb he
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at ha
    simp only [List.mem_range'_1] at hb
    dsimp only [Wire] at *
    omega
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WindowPhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ModularPhysical -/
section Port_ModularPhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem constantStraight_wellFormed {n s e : Nat} (q : Wire) (p : Straight n s e)
    (h : p.WellFormed) : (constantStraight q p).WellFormed := by
  have ht (g : TemplateGate n) (hg : g.WellFormed) : (constantTemplateGate q g).WellFormed := by
    cases g <;> exact constantControlGate_wellFormed q _ hg
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨ht g h.1,ih h.2⟩
  | recordGate i v g p ih => exact ⟨constantControlGate_wellFormed q g h.1,ih h.2⟩
  | measure w p ih => exact ih h

theorem uncontrolledCompareProgram_wellFormed (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (hd : input.length=dirty.length)
    (hnd : ([c,r,t,f]++input++dirty).Nodup) :
    (uncontrolledCompareProgram n start input dirty threshold c r t f).2.WellFormed := by
  apply constantStraight_wellFormed
  apply compareGEProgram_wellFormed _ _ _ _ _ _ _ _ _ _ hd
  change (gidneyCompareVirtualControl input dirty c r t f :: ([c,r,t,f]++input++dirty)).Nodup
  refine List.nodup_cons.mpr ⟨?_,hnd⟩
  intro hm
  have hh : ([c,r,t,f]++input++dirty).sum+1 ≤ ([c,r,t,f]++input++dirty).sum := List.le_sum_of_mem hm
  exact (Nat.not_succ_le_self _) hh

attribute [local irreducible] uncontrolledCompareProgram gidneyProgram

theorem modularAddProgram_wellFormed (n start : Nat) (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=correction.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    (modularAddProgram n start input acc correction p q c r t f).2.WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length=(input.take (acc.length-1)).length+1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularAddProgram
  apply straight_append_wellFormed
  · exact literalProgram_wellFormed _ (controlledAddCarry_wellFormed input acc q c f hlen hl.1)
  · apply appendCompiled_wellFormed
    · exact uncontrolledCompareProgram_wellFormed _ _ acc input p c r t f hlen.symm hl.2.1
    · apply straight_append_wellFormed
      · exact gidneyProgram_wellFormed _ _ acc _ correction f c r t hd hk.symm hl.2.2.1
      · exact literalProgram_wellFormed _ (controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2)

theorem modularSubProgram_wellFormed (n start : Nat) (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=modulus.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    (modularSubProgram n start input acc modulus p q c r t f).2.WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length=(input.take (acc.length-1)).length+1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularSubProgram
  apply prependCompiled_wellFormed
  · exact controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ acc _ modulus f c r t hd hk.symm hl.2.2.1
    · apply appendCompiled_wellFormed
      · exact uncontrolledCompareProgram_wellFormed _ _ acc input p c r t f hlen.symm hl.2.1
      · apply literalProgram_wellFormed
        exact (circuitWellFormed_adjoint _).mpr (controlledAddCarry_wellFormed input acc q c f hlen hl.1)

theorem modularDoubleProgram_wellFormed (n start : Nat) (a : Wire) (rest dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a::rest).length=bits.length) (hd : (a::rest).length=dirty.length)
    (hnd : ([c,r,t,f]++(a::rest)++dirty).Nodup) :
    (modularDoubleProgram n start (a::rest) dirty bits p c r t f).2.WellFormed := by
  have hl := doubling_layout (a::rest) dirty c r t f hnd
  have htlen : (a::rest).length=(dirty.take rest.length).length+1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  have hshort : ([f,c,r,t]++(a::rest)++dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t]++(a::rest))).append (List.take_sublist _ _)) hl.2
  unfold modularDoubleProgram
  apply prependCompiled_wellFormed
  · exact doublingShift_wellFormed a f rest hl.1
  · apply appendCompiled_wellFormed
    · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
    · apply appendCompiled_wellFormed
      · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ htlen hk.symm hshort
      · apply literalProgram_wellFormed
        have hfa : f≠a := fun he => (List.nodup_cons.mp hl.1).1 (by simp [he])
        simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa]

theorem modularHalveProgram_wellFormed (n start : Nat) (a : Wire) (rest dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a::rest).length=bits.length) (hd : (a::rest).length=dirty.length)
    (hnd : ([c,r,t,f]++(a::rest)++dirty).Nodup) :
    (modularHalveProgram n start (a::rest) dirty bits p c r t f).2.WellFormed := by
  have hl := doubling_layout (a::rest) dirty c r t f hnd
  have htlen : (a::rest).length=(dirty.take rest.length).length+1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  have hshort : ([f,c,r,t]++(a::rest)++dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t]++(a::rest))).append (List.take_sublist _ _)) hl.2
  unfold modularHalveProgram
  apply prependCompiled_wellFormed
  · have hfa : f≠a := fun he => (List.nodup_cons.mp hl.1).1 (by simp [he])
    simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa]
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ htlen hk.symm hshort
    · apply appendCompiled_wellFormed
      · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
      · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (doublingShift_wellFormed a f rest hl.1))

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([c,r,t,f]++controls++input++(a::rest)).Nodup) :
    (hornerProgram n start controls input (a::rest) bits p c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [hornerProgram]
    apply appendCompiled_wellFormed
    · exact ih _ (horner_tail_layout q qs input (a::rest) c r t f hnd)
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(hornerProgram n start qs input (a::rest) bits p c r t f).1)
          (start+(hornerProgram n start qs input (a::rest) bits p c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · exact modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
          (horner_add_layout q qs input (a::rest) c r t f hnd)
      · apply appendCompiled_wellFormed
        · exact modularDoubleProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout (q::qs) input (a::rest) c r t f hnd)
        · exact modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
            (horner_add_layout q qs input (a::rest) c r t f hnd)

theorem hornerInverseProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([c,r,t,f]++controls++input++(a::rest)).Nodup) :
    (hornerInverseProgram n start controls input (a::rest) bits p c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [hornerInverseProgram]
    apply appendCompiled_wellFormed
    · exact modularSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
        (horner_add_layout q qs input (a::rest) c r t f hnd)
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(modularSubProgram n start input (a::rest) bits p q c r t f).1)
          (start+(modularSubProgram n start input (a::rest) bits p q c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · trivial
      · apply appendCompiled_wellFormed
        · exact modularHalveProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout (q::qs) input (a::rest) c r t f hnd)
        · exact ih _ (horner_tail_layout q qs input (a::rest) c r t f hnd)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ModularPhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEACenterPhysical -/
section Port_EEACenterPhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] gidneyProgram uncontrolledCompareProgram

theorem constMinusProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length=dirty.length+1) (hk : input.length=bits.length)
    (hnd : ([q,c,r,t]++input++dirty).Nodup) :
    (constMinusProgram n start input dirty bits q c r t).2.WellFormed := by
  unfold constMinusProgram
  apply prependCompiled_wellFormed
  · exact (controlledConstMinus_wellFormed input dirty bits q c r t hk hd hnd).1
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ hd (by simp) hnd
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hk.symm hnd

private theorem port_EEACenterPhysical_center_layout (input dirty : List Wire) (c r t iter : Wire)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup) :
    ([iter,c,r,t] ++ input ++ dirty.take (input.length - 1)).Nodup := by
  have hp : ([c,r,t,iter] ++ input ++ dirty).Perm ([iter,c,r,t] ++ input ++ dirty) :=
    ((show ([c,r,t] ++ [iter]).Perm ([iter] ++ [c,r,t]) from
      List.perm_append_comm).append_right input).append_right dirty
  exact (hp.nodup_iff.mp hnd).sublist
    ((List.Sublist.refl _).append (List.take_sublist _ _))

attribute [local irreducible] constMinusProgram

theorem eeaCenterProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length)
    (hk : input.length=bits.length) (hpos : 0 < input.length)
    (hnd : ([c,r,t,iter]++input++dirty).Nodup) :
    (eeaCenterProgram n start input dirty bits p c r t iter).2.WellFormed := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaCenterProgram
  apply appendCompiled_wellFormed
  · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
  · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ ht hk (port_EEACenterPhysical_center_layout input dirty c r t iter hnd)

theorem eeaUncenterProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length)
    (hk : input.length=bits.length) (hpos : 0 < input.length)
    (hnd : ([c,r,t,iter]++input++dirty).Nodup) :
    (eeaUncenterProgram n start input dirty bits p c r t iter).2.WellFormed := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaUncenterProgram
  apply appendCompiled_wellFormed
  · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ ht hk (port_EEACenterPhysical_center_layout input dirty c r t iter hnd)
  · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
theorem eeaParityProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length=dirty.length+1) (hk : input.length=bits.length)
    (hnd : ([iter,c,r,t]++input++dirty).Nodup) :
    (eeaParityProgram n start input dirty bits c r t iter).2.WellFormed := by
  unfold eeaParityProgram
  apply prependCompiled_wellFormed
  · simp [CircuitWellFormed,Gate.WellFormed]
  · apply appendCompiled_wellFormed
    · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hk hnd
    · exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])



theorem adaptive_seq_wellFormed_parts (first second : AdaptiveCircuit)
    (h : (first.seq second).WellFormed) : first.WellFormed ∧ second.WellFormed := by
  induction first with
  | done => exact ⟨trivial,h⟩
  | unitary gs next ih =>
    have hh := ih h.2
    exact ⟨⟨h.1,hh.1⟩,hh.2⟩
  | xMeasureReset w p q ihp ihq =>
    have hp := ihp h.1
    have hq := ihq h.2
    exact ⟨⟨hp.1,hq.1⟩,hp.2⟩

private theorem port_EEACenterPhysical_preprocessCenter_layout :
    ([560,561,562,2] ++ (List.range' 266 256).reverse ++ List.range' 4 256).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨by decide,
    by simpa using (List.nodup_range' (s := 266) (n := 256)), ?_⟩,
    List.nodup_range', ?_⟩
  · intro a ha b hb he
    simp at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · intro a ha b hb he
    simp at ha hb
    rcases ha with ha | ha
    · rcases ha with rfl | rfl | rfl | rfl; omega
    · omega

private theorem port_EEACenterPhysical_parity_layout :
    ([2,560,561,562]++List.range' 263 256++List.range' 4 255).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

attribute [local irreducible] eeaCenterProgram eeaUncenterProgram eeaParityProgram
  eeaCenter eeaUncenter eeaLengthSetup eeaLengthUndo workRegistersPrepare workRegistersRestore

theorem preprocessProgram_wellFormed (n start : Nat) : (preprocessProgram n start).2.WellFormed := by
  unfold preprocessProgram
  apply surroundCompiled_wellFormed
  · exact workRegistersPrepare_resources.1
  · exact (adaptive_seq_wellFormed_parts (eeaCenter (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2) (.unitary eeaLengthSetup .done) eeaPreprocess_wellFormed.2).2.1
  · exact eeaCenterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) port_EEACenterPhysical_preprocessCenter_layout

theorem unpreprocessProgram_wellFormed (n start : Nat) : (unpreprocessProgram n start).2.WellFormed := by
  unfold unpreprocessProgram
  apply surroundCompiled_wellFormed
  · exact eeaUnpreprocess_wellFormed.1
  · exact workRegistersRestore_resources.1
  · exact eeaUncenterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) port_EEACenterPhysical_preprocessCenter_layout

theorem productionParityProgram_wellFormed (n start : Nat) : (productionParityProgram n start).2.WellFormed := by
  unfold productionParityProgram
  exact eeaParityProgram_wellFormed _ _ _ _ _ _ _ _ _ (by simp) (by simp [secp256k1ModulusBits]) port_EEACenterPhysical_parity_layout
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEACenterPhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEAStructuralPhysical -/
section Port_EEAStructuralPhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem vchainTailProgram_wellFormed (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat)
    (h : (mcxVChainTailAdaptive acc controls target scratch).WellFormed) :
    (vchainTailProgram n controls acc target scratch start).2.WellFormed := by
  induction controls generalizing acc scratch start with
  | nil => trivial
  | cons control controls ih =>
    cases controls with
    | nil => exact literalProgram_wellFormed _ h.1
    | cons next controls =>
      cases scratch with
      | nil => trivial
      | cons work scratch =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2
        apply prependCompiled_wellFormed
        · exact h.1
        · apply appendCompiled_wellFormed
          · exact ih work scratch start hs.1
          · apply andEraseProgram_wellFormed
            have hg := h.1 (.CCX control acc work) (by simp)
            exact hg.1

theorem vchainProgram_wellFormed (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (h : (mcxVChainAdaptive controls target scratch).WellFormed) :
    (vchainProgram n start controls target scratch).2.WellFormed := by
  cases controls with
  | nil => exact literalProgram_wellFormed _ h.1
  | cons first rest =>
    cases rest with
    | nil => exact literalProgram_wellFormed _ h.1
    | cons second rest => exact vchainTailProgram_wellFormed _ _ _ _ _ _ h

attribute [local irreducible] vchainProgram

theorem rippleMajProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledMajAdaptive control target addend carry scratch).WellFormed) :
    (rippleMajProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleMajProgram
  exact prependCompiled_wellFormed _ _ h.1 (vchainProgram_wellFormed _ _ _ _ _ h.2)

theorem rippleUmaInvProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledUmaInvAdaptive control target addend carry scratch).WellFormed) :
    (rippleUmaInvProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleUmaInvProgram
  exact prependCompiled_wellFormed _ _ h.1 (vchainProgram_wellFormed _ _ _ _ _ h.2)

theorem rippleUmaProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledUmaAdaptive control target addend carry scratch).WellFormed) :
    (rippleUmaProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleUmaProgram
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem rippleMajInvProgram_wellFormed (n start : Nat) (control target addend carry scratch : Wire)
    (h : (controlledMajInvAdaptive control target addend carry scratch).WellFormed) :
    (rippleMajInvProgram n start control target addend carry scratch).2.WellFormed := by
  unfold rippleMajInvProgram
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem rippleFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (h : (rippleFirstCellAdaptive mode control target addend carry scratch).WellFormed) :
    (rippleFirstProgram n start mode control target addend carry scratch).2.WellFormed := by
  cases mode with
  | add => exact rippleMajProgram_wellFormed _ _ _ _ _ _ _ h
  | sub => exact rippleUmaInvProgram_wellFormed _ _ _ _ _ _ _ h

theorem rippleSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (h : (rippleSecondCellAdaptive mode control target addend carry scratch).WellFormed) :
    (rippleSecondProgram n start mode control target addend carry scratch).2.WellFormed := by
  cases mode with
  | add => exact rippleUmaProgram_wellFormed _ _ _ _ _ _ _ h
  | sub => exact rippleMajInvProgram_wellFormed _ _ _ _ _ _ _ h


theorem sequenceCircuit_wellFormed_members (sources : List AdaptiveCircuit)
    (h : (sequenceCircuit sources).WellFormed) : ∀ source ∈ sources, source.WellFormed := by
  induction sources with
  | nil => simp
  | cons source rest ih =>
    have hs := adaptive_seq_wellFormed_parts source (sequenceCircuit rest) h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hs.1
    · exact ih hs.2 c hc

theorem phaseSegments_wellFormed (n : Nat) (r : PhaseUpdateRegisters) (shift : Wire) (core : Circuit)
    (h : (sequenceCircuit (phaseSources r shift core)).WellFormed) :
    ∀ seg ∈ phaseSegments n r shift core, ∀ start, (seg start).2.WellFormed := by
  have hs := sequenceCircuit_wellFormed_members _ h
  have ha := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthQ (r.withShiftEpoch shift).zeroQ (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hb := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthRPrime (r.withShiftEpoch shift).zeroRPrime (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hc := hs (mcxVChainAdaptive (r.withShiftEpoch shift).lengthS (r.withShiftEpoch shift).zeroS (r.withShiftEpoch shift).equalityScratch) (by simp [phaseSources])
  have hg := (hs (.unitary core .done) (by simp [phaseSources])).1
  intro seg hm start
  simp only [phaseSegments,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact vchainProgram_wellFormed _ _ _ _ _ ha
    | exact vchainProgram_wellFormed _ _ _ _ _ hb
    | exact vchainProgram_wellFormed _ _ _ _ _ hc
    | exact literalProgram_wellFormed _ hg
    | exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])

theorem phaseProgram_wellFormed (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (h : (phaseUpdateEpochAdaptive r shift).WellFormed) : (phaseProgram n start r shift).2.WellFormed := by
  apply sequenceProgram_wellFormed
  apply phaseSegments_wellFormed
  rwa [phaseSources_forward]

theorem phaseInverseProgram_wellFormed (n start : Nat) (r : PhaseUpdateRegisters) (shift : Wire)
    (h : (phaseUpdateEpochInverseAdaptive r shift).WellFormed) : (phaseInverseProgram n start r shift).2.WellFormed := by
  apply sequenceProgram_wellFormed
  apply phaseSegments_wellFormed
  rwa [phaseSources_inverse]


theorem zeroEraseProgram_wellFormed (n start : Nat) (a b w : Wire) (hab : a ≠ b) :
    (zeroEraseProgram n start a b w).2.WellFormed := by
  apply prependCompiled_wellFormed
  · simp [CircuitWellFormed,Gate.WellFormed]
  · exact appendCompiled_wellFormed _ _ (andEraseProgram_wellFormed _ _ _ _ _ hab)
      (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed]))

theorem unaryProgram_wellFormed (n : Nat) (order : UnaryOrder)
    (leaf : Nat → Wire → (start : Nat) → (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → AdaptiveCircuit)
    (hleaf : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (h : (unaryAdaptiveAction order source tree control paths).WellFormed) :
    (unaryProgram n order leaf tree control paths start).2.WellFormed := by
  let WF := fun (start : Nat) (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF start _
  induction tree generalizing control paths start with
  | leaf label =>
    simp only [unaryProgram]
    exact hleaf label control start h
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp only [unaryProgram]; trivial
    | cons path rest =>
      cases order with
      | inc =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2
        have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
        have hab := (h.1 (.CCX control bit path) (by simp [computeZeroAnd])).1
        simp only [unaryProgram]
        apply prependCompiled_wellFormed _ _ h.1
        apply appendCompiled_wellFormed _ _ (ihz _ _ _ hs.1)
        apply prependCompiled_wellFormed _ _ hs.2.1
        apply appendCompiled_wellFormed _ _ (iho _ _ _ ht.1)
        exact prependCompiled_wellFormed _ _ ht.2.1 (zeroEraseProgram_wellFormed _ _ _ _ _ hab)
      | dec =>
        have hs := adaptive_seq_wellFormed_parts _ _ h.2.2
        have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
        have hab := (h.1 (.CCX control bit path) (by simp [computeZeroAnd])).1
        simp only [unaryProgram]
        apply prependCompiled_wellFormed _ _ h.1
        apply prependCompiled_wellFormed _ _ h.2.1
        apply appendCompiled_wellFormed _ _ (iho _ _ _ hs.1)
        apply prependCompiled_wellFormed _ _ hs.2.1
        exact appendCompiled_wellFormed _ _ (ihz _ _ _ ht.1) (zeroEraseProgram_wellFormed _ _ _ _ _ hab)


attribute [local irreducible] rippleFirstProgram rippleSecondProgram

theorem coefficientFirstProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (h : (coefficientPrefixFirstLeafAdaptive r k K mode target label control).WellFormed) :
    (coefficientFirstProgram n start r k K mode target label control).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (literalProgram_wellFormed _ hs.2.1)

theorem coefficientSecondProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (h : (coefficientPrefixSecondLeafAdaptive r k K mode target label control).WellFormed) :
    (coefficientSecondProgram n start r k K mode target label control).2.WellFormed :=
  prependCompiled_wellFormed _ _ h.1 (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ h.2)

attribute [local irreducible] coefficientFirstProgram coefficientSecondProgram

theorem coefficientProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (h : (coefficientPrefixAdaptive r k K mode signUpdate target).WellFormed) :
    (coefficientProgram n start r k K mode signUpdate target).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
  unfold coefficientProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact unaryProgram_wellFormed _ _ _ _
      (fun label control cursor h => coefficientFirstProgram_wellFormed n cursor r k K mode target label control h) _ _ _ _ hs.1
  · apply prependCompiled_wellFormed _ _ hs.2.1
    apply appendCompiled_wellFormed
    · exact unaryProgram_wellFormed _ _ _ _
        (fun label control cursor h => coefficientSecondProgram_wellFormed n cursor r k K mode target label control h) _ _ _ _ ht.1
    · exact literalProgram_wellFormed _ ht.2.1

theorem coefficientInverseProgram_wellFormed (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (h : (coefficientPrefixInverseAdaptive r k K mode signUpdate target).WellFormed) :
    (coefficientInverseProgram n start r k K mode signUpdate target).2.WellFormed :=
  coefficientProgram_wellFormed _ _ _ _ _ _ _ _ h
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEAStructuralPhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.EEAIntervalPhysical -/
section Port_EEAIntervalPhysical

/-! Structural preservation of gate validity. Generic lemmas assume source syntax validity;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] terminalWork1Clear

theorem dualEraseProgram_wellFormed (n start : Nat) (a i x b j y : Wire) (ha : a ≠ i) (hb : b ≠ j) :
    (dualEraseProgram n start a i x b j y).2.WellFormed :=
  appendCompiled_wellFormed _ _ (zeroEraseProgram_wellFormed _ _ _ _ _ hb)
    (zeroEraseProgram_wellFormed _ _ _ _ _ ha)

theorem dualProgram_wellFormed (n : Nat) (order : UnaryOrder)
    (leaf : Nat → Wire → Wire → (start : Nat) → (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → Wire → AdaptiveCircuit)
    (hleaf : ∀ label a b start, (source label a b).WellFormed → (leaf label a b start).2.WellFormed)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat)
    (h : (dualUnaryAdaptiveAction order source tree a b xs ys).WellFormed) :
    (dualProgram n order leaf tree a b xs ys start).2.WellFormed := by
  let WF := fun (start : Nat) (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF start _
  induction tree generalizing a b xs ys start with
  | leaf label => simp only [dualProgram]; exact hleaf label a b start h
  | node i j zero one ihz iho =>
    cases xs with
    | nil => simp only [dualProgram]; trivial
    | cons x xs =>
      cases ys with
      | nil => simp only [dualProgram]; trivial
      | cons y ys =>
        cases order with
        | inc =>
          have hs := adaptive_seq_wellFormed_parts _ _ h.2.2
          have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
          have ha := (h.1 (.CCX a i x) (by simp [computeZeroAnd])).1
          have hb := (h.2.1 (.CCX b j y) (by simp [computeZeroAnd])).1
          simp only [dualProgram]
          apply prependCompiled_wellFormed _ _ h.1
          apply prependCompiled_wellFormed _ _ h.2.1
          apply appendCompiled_wellFormed _ _ (ihz _ _ _ _ _ hs.1)
          apply prependCompiled_wellFormed _ _ hs.2.1
          apply appendCompiled_wellFormed _ _ (iho _ _ _ _ _ ht.1)
          exact prependCompiled_wellFormed _ _ ht.2.1 (dualEraseProgram_wellFormed _ _ _ _ _ _ _ _ ha hb)
        | dec =>
          have hs := adaptive_seq_wellFormed_parts _ _ h.2.2.2
          have ht := adaptive_seq_wellFormed_parts _ _ hs.2.2
          have ha := (h.1 (.CCX a i x) (by simp [computeZeroAnd])).1
          have hb := (h.2.1 (.CCX b j y) (by simp [computeZeroAnd])).1
          simp only [dualProgram]
          apply prependCompiled_wellFormed _ _ h.1
          apply prependCompiled_wellFormed _ _ h.2.1
          apply prependCompiled_wellFormed _ _ h.2.2.1
          apply appendCompiled_wellFormed _ _ (iho _ _ _ _ _ hs.1)
          apply prependCompiled_wellFormed _ _ hs.2.1
          exact appendCompiled_wellFormed _ _ (ihz _ _ _ _ _ ht.1) (dualEraseProgram_wellFormed _ _ _ _ _ _ _ _ ha hb)


theorem equalityProgram_wellFormed (n start : Nat) (register : List Wire) (value : Nat) (flag : Wire)
    (scratch : List Wire)
    (h : (computeEqConstAdaptive register value flag scratch).WellFormed) :
    (equalityProgram n start register value flag scratch).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (vchainProgram_wellFormed _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem toggleEqualityProgram_wellFormed (n start : Nat) (root : Wire) (register : List Wire) (value : Nat)
    (acc flag : Wire) (scratch : List Wire)
    (h : (toggleEqConstUnderControlAdaptive root register value acc flag scratch).WellFormed) :
    (toggleEqualityProgram n start root register value acc flag scratch).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  exact appendCompiled_wellFormed _ _ (equalityProgram_wellFormed _ _ _ _ _ _ hs.1)
    (prependCompiled_wellFormed _ _ hs.2.1 (equalityProgram_wellFormed _ _ _ _ _ _ hs.2.2))

theorem intervalFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire)
    (h : (intervalFirstLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).WellFormed) :
    (intervalFirstProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem intervalSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc target addend carry scratch : Wire) (label : Nat)
    (rightControl leftControl : Wire)
    (h : (intervalSecondLeafAdaptive mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).WellFormed) :
    (intervalSecondProgram n start mode topSpecial rightTop leftTop acc target addend carry scratch label rightControl leftControl).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
      (literalProgram_wellFormed _ hs.2.1))

theorem topFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (h : (topSpecialFirstLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).WellFormed) :
    (topFirstProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  exact appendCompiled_wellFormed _ _ (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (rippleFirstProgram_wellFormed _ _ _ _ _ _ _ _ ht.1)
      (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ ht.2))

theorem topSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (value : Nat)
    (rightRegister leftRegister : List Wire) (acc target addend carry work flag : Wire)
    (scratch : List Wire) (rightRoot leftRoot : Wire)
    (h : (topSpecialSecondLeafAdaptive mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).WellFormed) :
    (topSecondProgram n start mode value rightRegister leftRegister acc target addend carry work flag scratch rightRoot leftRoot).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  exact appendCompiled_wellFormed _ _ (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (rippleSecondProgram_wellFormed _ _ _ _ _ _ _ _ ht.1)
      (toggleEqualityProgram_wellFormed _ _ _ _ _ _ _ _ ht.2))


theorem traversalFirstProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (h : (intervalFirstTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed) :
    (traversalFirstProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.WellFormed := by
  unfold traversalFirstProgram
  apply dualProgram_wellFormed _ _ _ _ ?_ _ _ _ _ _ _ h
  intro label right left cursor hh
  exact intervalFirstProgram_wellFormed n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left hh

theorem traversalSecondProgram_wellFormed (n start : Nat) (mode : RippleMode) (topSpecial : Bool)
    (rightTop leftTop acc carry scratch : Wire) (targetAt addendAt : Nat → Wire)
    (tree : DualUnaryActionTree) (rightRoot leftRoot : Wire) (rightPaths leftPaths : List Wire)
    (h : (intervalSecondTraversalAdaptive mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).WellFormed) :
    (traversalSecondProgram n start mode topSpecial rightTop leftTop acc carry scratch targetAt addendAt tree rightRoot leftRoot rightPaths leftPaths).2.WellFormed := by
  unfold traversalSecondProgram
  apply dualProgram_wellFormed _ _ _ _ ?_ _ _ _ _ _ _ h
  intro label right left cursor hh
  exact intervalSecondProgram_wellFormed n cursor mode topSpecial rightTop leftTop acc (targetAt label) (addendAt label) carry scratch label right left hh


theorem intervalTopFirstProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (h : (if intervalHasTopSpecial k K then topSpecialFirstLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).WellFormed) :
    (intervalTopFirstProgram n start r k K mode target).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold intervalTopFirstProgram
  split
  · rename_i he
    simp only [he,ite_true] at h
    exact topFirstProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · trivial

theorem intervalTopSecondProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (k K : Nat)
    (mode : RippleMode) (target : IntervalTarget)
    (h : (if intervalHasTopSpecial k K then topSpecialSecondLeafAdaptive mode (intervalTopRelative k K) r.lengthS r.lengthQ (r.accumulator k K) (r.targetAt target (intervalTopRelative k K)) (r.addendAt target (intervalTopRelative k K)) (r.carry k K) (r.cellScratch k K) (r.cellScratch k K) (r.equalityScratch k K) r.control r.control else .unitary [] .done).WellFormed) :
    (intervalTopSecondProgram n start r k K mode target).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold intervalTopSecondProgram
  split
  · rename_i he
    simp only [he,ite_true] at h
    exact topSecondProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · trivial

attribute [local irreducible] intervalTopFirstProgram intervalTopSecondProgram traversalFirstProgram traversalSecondProgram

theorem intervalProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : (intervalAddSub r width k K mode signUpdate target).WellFormed) :
    (intervalProgram n start r width k K mode signUpdate target).2.WellFormed := by
  have h0 := adaptive_seq_wellFormed_parts _ _ h
  have h1 := adaptive_seq_wellFormed_parts _ _ h0.2
  have h2 := adaptive_seq_wellFormed_parts _ _ h1.2
  have h3 := adaptive_seq_wellFormed_parts _ _ h2.2
  have h4 := adaptive_seq_wellFormed_parts _ _ h3.2
  have h5 := adaptive_seq_wellFormed_parts _ _ h4.2
  unfold intervalProgram
  apply prependCompiled_wellFormed _ _ h0.1.1
  apply appendCompiled_wellFormed _ _ (intervalTopFirstProgram_wellFormed _ _ _ _ _ _ _ h1.1)
  apply appendCompiled_wellFormed
  · exact traversalFirstProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2.1
  · apply prependCompiled_wellFormed _ _ h3.1.1
    apply appendCompiled_wellFormed
    · exact traversalSecondProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h4.1
    · exact appendCompiled_wellFormed _ _ (intervalTopSecondProgram_wellFormed _ _ _ _ _ _ _ h5.1)
        (literalProgram_wellFormed _ h5.2.1)


theorem intervalInverseProgram_wellFormed (n start : Nat) (r : IntervalRegisters) (width k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : IntervalTarget)
    (h : (intervalAddSubInverse r width k K mode signUpdate target).WellFormed) :
    (intervalInverseProgram n start r width k K mode signUpdate target).2.WellFormed :=
  intervalProgram_wellFormed _ _ _ _ _ _ _ _ _ h

theorem sequenceProgram_wellFormed_of_source (n start : Nat) (ps : List (FixedSegment n)) (sources : List AdaptiveCircuit)
    (h : (sequenceCircuit sources).WellFormed)
    (hp : List.Forall₂ (fun p source => ∀ start, source.WellFormed → (p start).2.WellFormed) ps sources) :
    (sequenceProgram n ps start).2.WellFormed := by
  induction hp generalizing start with
  | nil => trivial
  | @cons p source ps sources hp hps ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (hp _ hs.1) (ih _ hs.2)

attribute [local irreducible] intervalProgram intervalInverseProgram coefficientProgram coefficientInverseProgram
  phaseProgram phaseInverseProgram intervalAddSub intervalAddSubInverse coefficientPrefixAdaptive coefficientPrefixInverseAdaptive
  phaseUpdateEpochAdaptive phaseUpdateEpochInverseAdaptive

theorem remainderBlockProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (h : (blockBAdaptive r width w).WellFormed) :
    (remainderBlockProgram n start r width w).2.WellFormed := by
  unfold remainderBlockProgram
  rw [← remainderBlockSources_eq r width w] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold remainderBlockSegments remainderBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalProgram_wellFormed n cursor (r.remainder w) width w.start w.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalProgram_wellFormed n cursor (r.remainder w) width w.start w.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem coefficientBlockProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width : Nat) (w : ActiveWindow)
    (h : (blockEAdaptive r width w).WellFormed) :
    (coefficientBlockProgram n start r width w).2.WellFormed := by
  unfold coefficientBlockProgram
  rw [← coefficientBlockSources_eq r width w] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold coefficientBlockSegments coefficientBlockSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientProgram_wellFormed n cursor (r.coefficient w) w.start w.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientProgram_wellFormed n cursor (r.coefficient w) w.start w.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram blockBAdaptive blockEAdaptive

theorem indexedStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (indexedStepAdaptive r width T).WellFormed) :
    (indexedStepProgram n start r width T).2.WellFormed := by
  unfold indexedStepProgram
  rw [← indexedStepSources_eq r width T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold indexedStepSegments indexedStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact remainderBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).remainder hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).coefficient hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact phaseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem indexedInverseStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (h : (indexedStepInverseAdaptive r 256 T).WellFormed) :
    (indexedInverseStepProgram n start r T).2.WellFormed := by
  unfold indexedInverseStepProgram
  rw [← indexedInverseStepSources_eq r T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold indexedInverseStepSegments indexedInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact phaseInverseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1


attribute [local irreducible] indexedStepProgram indexedInverseStepProgram indexedStepAdaptive indexedStepInverseAdaptive

theorem scheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (width count first start : Nat)
    (h : (indexedScheduleAdaptive r width first count).WellFormed) :
    (scheduleProgram n r width count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (indexedStepProgram_wellFormed _ _ _ _ _ hs.1)
      (ih _ _ hs.2)

theorem inverseScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (h : (indexedScheduleInverseAdaptive r 256 first count).WellFormed) :
    (inverseScheduleProgram n r count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (ih _ _ hs.1)
      (indexedInverseStepProgram_wellFormed _ _ _ _ hs.2)

attribute [local irreducible] scheduleProgram inverseScheduleProgram indexedScheduleAdaptive indexedScheduleInverseAdaptive

theorem eeaForwardProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1EEAForwardAdaptive r).WellFormed) : (eeaForwardProgram n start r).2.WellFormed :=
  scheduleProgram_wellFormed _ _ _ _ _ _ h

theorem eeaReverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1EEAReverseAdaptive r).WellFormed) : (eeaReverseProgram n start r).2.WellFormed :=
  inverseScheduleProgram_wellFormed _ _ _ _ _ h


attribute [local irreducible] eeaForwardProgram eeaReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1EEAForwardAdaptive secp256k1EEAReverseAdaptive eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

theorem forwardWrapperProgram_wellFormed (n start : Nat) : (forwardWrapperProgram n start).2.WellFormed := by
  have h := secp256k1EEAForwardWrapper_wellFormed
  unfold forwardWrapperProgram
  rw [← forwardWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold forwardWrapperSegments forwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact preprocessProgram_wellFormed n cursor
  · intro cursor hh
    exact eeaForwardProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem reverseWrapperProgram_wellFormed (n start : Nat) : (reverseWrapperProgram n start).2.WellFormed := by
  have h := secp256k1EEAReverseWrapper_wellFormed
  unfold reverseWrapperProgram
  rw [← reverseWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold reverseWrapperSegments reverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact eeaReverseProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact unpreprocessProgram_wellFormed n cursor
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_EEAIntervalPhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.MeasuredEEAPhysical -/
section Port_MeasuredEEAPhysical

/-! Structural preservation of gate validity. Generic lemmas assume source syntax validity;
production wrapper lemmas discharge that premise using the fixed source layouts. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] terminalWork1Clear

theorem zeroCellProgram_wellFormed (n start : Nat) (base : Bool) (r bit guard target temporary : Wire)
    (h : (measuredZeroCell base r bit guard target temporary).WellFormed) :
    (zeroCellProgram n start base r bit guard target temporary).2.WellFormed := by
  apply prependCompiled_wellFormed _ _ h.1
  exact andEraseProgram_wellFormed _ _ _ _ _
    (h.1 (.CCX r bit temporary) (by simp [measuredZeroPrefix])).1

theorem upperForwardLeafProgram_wellFormed (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredUpperForwardLeaf k K control temporary bitAt dirtyAt label r).WellFormed) :
    (upperForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold upperForwardLeafProgram
  unfold measuredUpperForwardLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · split <;> rename_i hd <;> (first | rw [if_pos hd] at h | rw [if_neg hd] at h)
    all_goals exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem upperReverseLeafProgram_wellFormed (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredUpperReverseLeaf k K temporary bitAt dirtyAt label r).WellFormed) :
    (upperReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold upperReverseLeafProgram
  unfold measuredUpperReverseLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem lowerForwardLeafProgram_wellFormed (n start : Nat) (k K : Nat) (control temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredLowerForwardLeaf k K control temporary bitAt dirtyAt label r).WellFormed) :
    (lowerForwardLeafProgram n start k K control temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold lowerForwardLeafProgram
  unfold measuredLowerForwardLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · split <;> rename_i hd <;> (first | rw [if_pos hd] at h | rw [if_neg hd] at h)
    all_goals exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem lowerReverseLeafProgram_wellFormed (n start : Nat) (k K : Nat) (temporary : Wire) (bitAt dirtyAt : Nat → Wire) (label : Nat) (r : Wire)
    (h : (measuredLowerReverseLeaf k K temporary bitAt dirtyAt label r).WellFormed) :
    (lowerReverseLeafProgram n start k K temporary bitAt dirtyAt label r).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold lowerReverseLeafProgram
  unfold measuredLowerReverseLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · exact zeroCellProgram_wellFormed _ _ _ _ _ _ _ _ h
  · trivial

theorem rangeLeafProgram_wellFormed (n : Nat) (after : Bool) (r : Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (hl : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (label : Nat) (dynamic : Wire) (start : Nat)
    (h : (measuredRangeLeaf after r source label dynamic).WellFormed) :
    (rangeLeafProgram n after r leaf label dynamic start).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold rangeLeafProgram
  unfold measuredRangeLeaf at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (hl _ _ _ hs.1) (literalProgram_wellFormed _ hs.2.1)
  · exact prependCompiled_wellFormed _ _ h.1 (hl _ _ _ h.2)

theorem rangeScanProgram_wellFormed (n : Nat) (after : Bool) (order : UnaryOrder)
    (tree : UnaryActionTree) (control r : Wire) (path : List Wire)
    (leaf : Nat → Wire → FixedSegment n) (source : Nat → Wire → AdaptiveCircuit)
    (hl : ∀ label control start, (source label control).WellFormed → (leaf label control start).2.WellFormed)
    (start : Nat) (h : (measuredRangeScan after order tree control r path source).WellFormed) :
    (rangeScanProgram n after order tree control r path leaf start).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold rangeScanProgram
  unfold measuredRangeScan at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · apply prependCompiled_wellFormed _ _ h.1
    exact unaryProgram_wellFormed n order _ _ (rangeLeafProgram_wellFormed n true r leaf source hl) tree control path start h.2
  · have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _
      (unaryProgram_wellFormed n order _ _ (rangeLeafProgram_wellFormed n false r leaf source hl) tree control path start hs.1)
      (literalProgram_wellFormed _ hs.2.1)

theorem upperMapProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (h : (measuredUpperZeroMap k K tree control r t path bitAt dirtyAt).WellFormed) :
    (upperMapProgram n k K tree control r t path bitAt dirtyAt start).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  unfold upperMapProgram
  apply appendCompiled_wellFormed
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => upperForwardLeafProgram_wellFormed n cursor k K control t bitAt dirtyAt label dynamic hh) _ hs.1
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => upperReverseLeafProgram_wellFormed n cursor k K t bitAt dirtyAt label dynamic hh) _ hs.2

theorem lowerMapProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (start : Nat)
    (h : (measuredLowerZeroMap k K tree control r t path bitAt dirtyAt).WellFormed) :
    (lowerMapProgram n k K tree control r t path bitAt dirtyAt start).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  unfold lowerMapProgram
  apply appendCompiled_wellFormed
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => lowerForwardLeafProgram_wellFormed n cursor k K control t bitAt dirtyAt label dynamic hh) _ hs.1
  · exact rangeScanProgram_wellFormed _ _ _ _ _ _ _ _ _
      (fun label dynamic cursor hh => lowerReverseLeafProgram_wellFormed n cursor k K t bitAt dirtyAt label dynamic hh) _ hs.2

theorem upperWriterProgram_wellFormed (n : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (h : (measuredHighestPositionWrite k K tree control r t path bitAt dirtyAt targets).WellFormed) :
    (upperWriterProgram n k K tree control r t path bitAt dirtyAt targets start).2.WellFormed := by
  unfold measuredHighestPositionWrite at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold upperWriterProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact upperMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.1
  · exact prependCompiled_wellFormed _ _ hs.2.1 (upperMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.2.2)

theorem lowerWriterProgram_wellFormed (n : Nat) (width : Nat) (k K : Nat) (tree : UnaryActionTree) (control r t : Wire) (path : List Wire) (bitAt dirtyAt : Nat → Wire) (targets : List Wire) (start : Nat)
    (h : (measuredRightLengthWrite width k K tree control r t path bitAt dirtyAt targets).WellFormed) :
    (lowerWriterProgram n width k K tree control r t path bitAt dirtyAt targets start).2.WellFormed := by
  unfold measuredRightLengthWrite at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold lowerWriterProgram
  apply prependCompiled_wellFormed _ _ h.1
  apply appendCompiled_wellFormed
  · exact lowerMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.1
  · exact prependCompiled_wellFormed _ _ hs.2.1 (lowerMapProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hs.2.2)

theorem ltUpdateProgram_wellFormed (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (h : (measuredLenUpdateLtUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed) :
    (ltUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.WellFormed := by
  unfold measuredLenUpdateLtUnary at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold ltUpdateProgram
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  apply surroundCompiled_wellFormed _ _ _ h.1 ht.2.1
  exact appendCompiled_wellFormed _ _ (upperWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hs.1)
    (upperWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ ht.1)

theorem lrpUpdateProgram_wellFormed (n : Nat) (width k K : Nat) (tree : UnaryActionTree) (control r t carry : Wire) (path : List Wire) (work1At work2At : Nat → Wire) (lengthT lengthRP constants : List Wire) (start : Nat)
    (h : (measuredLenUpdateLrpUnary width k K tree control r t carry path work1At work2At lengthT lengthRP constants).WellFormed) :
    (lrpUpdateProgram n width k K tree control r t carry path work1At work2At lengthT lengthRP constants start).2.WellFormed := by
  unfold measuredLenUpdateLrpUnary at h
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold lrpUpdateProgram
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  apply surroundCompiled_wellFormed _ _ _ h.1 ht.2.1
  exact appendCompiled_wellFormed _ _ (lowerWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hs.1)
    (lowerWriterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ ht.1)

theorem upperEndProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndUpper r width w).WellFormed) :
    (upperEndProgram n start r width w).2.WellFormed := by
  exact ltUpdateProgram_wellFormed n width w.k4 w.K4 (r.upperTree w) r.control (r.rangeAccumulator w.k4 w.K4) (r.temporary w.k4 w.K4) r.carry (r.path w.k4 w.K4) r.work1At r.work2At r.lengthT r.lengthRP r.constants start h

theorem lowerEndProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndLower r width w).WellFormed) :
    (lowerEndProgram n start r width w).2.WellFormed := by
  exact lrpUpdateProgram_wellFormed n width w.k5 (w.K5Decode width) (r.lowerTree width w) r.control (r.rangeAccumulator w.k5 (w.K5Decode width)) (r.temporary w.k5 (w.K5Decode width)) r.carry (r.path w.k5 (w.K5Decode width)) r.work1At r.work2At r.lengthT r.lengthRP r.constants start h

theorem endProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndIteration r width w).WellFormed) :
    (endProgram n start r width w).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h.2
  unfold endProgram
  exact prependCompiled_wellFormed _ _ h.1
    (appendCompiled_wellFormed _ _ (upperEndProgram_wellFormed _ _ _ _ _ hs.1)
      (lowerEndProgram_wellFormed _ _ _ _ _ hs.2))

theorem endInverseProgram_wellFormed (n start : Nat) (r : EndIterationRegisters) (width : Nat) (w : EndIterationWindows)
    (h : (measuredEndIterationInverse r width w).WellFormed) :
    (endInverseProgram n start r width w).2.WellFormed := by
  have hs := adaptive_seq_wellFormed_parts _ _ h
  have ht := adaptive_seq_wellFormed_parts _ _ hs.2
  unfold endInverseProgram
  exact appendCompiled_wellFormed _ _ (lowerEndProgram_wellFormed _ _ _ _ _ hs.1)
    (appendCompiled_wellFormed _ _ (upperEndProgram_wellFormed _ _ _ _ _ ht.1)
      (literalProgram_wellFormed _ ht.2.1))

theorem hProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredBlockHForward r width T).WellFormed) :
    (hProgram n start r width T).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold hProgram
  unfold measuredBlockHForward at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h.2
    exact surroundCompiled_wellFormed _ _ _ h.1 hs.2.1 (endProgram_wellFormed _ _ _ _ _ hs.1)
  · trivial

theorem hInverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredBlockHInverse r width T).WellFormed) :
    (hInverseProgram n start r width T).2.WellFormed := by
  let WF := fun (cp : (count : Nat) × Straight n start (start+count)) => cp.2.WellFormed
  change WF _
  unfold hInverseProgram
  unfold measuredBlockHInverse at h
  split <;> rename_i hc <;> (first | rw [if_pos hc] at h | rw [if_neg hc] at h)
  · have hs := adaptive_seq_wellFormed_parts _ _ h.2
    exact surroundCompiled_wellFormed _ _ _ h.1 hs.2.1 (endInverseProgram_wellFormed _ _ _ _ _ hs.1)
  · trivial

attribute [local irreducible] remainderBlockProgram coefficientBlockProgram phaseProgram phaseInverseProgram coefficientInverseProgram intervalInverseProgram
theorem measuredStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (width T : Nat)
    (h : (measuredIndexedStep r width T).WellFormed) :
    (measuredStepProgram n start r width T).2.WellFormed := by
  unfold measuredStepProgram
  rw [← measuredStepSources_eq r width T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredStepSegments measuredStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact remainderBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).remainder hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientBlockProgram_wellFormed n cursor r width (certifiedActiveWindows width T).coefficient hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact phaseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact hProgram_wellFormed n cursor r width T hh

theorem measuredInverseStepProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters) (T : Nat)
    (h : (measuredIndexedStepInverse r 256 T).WellFormed) :
    (measuredInverseStepProgram n start r T).2.WellFormed := by
  unfold measuredInverseStepProgram
  rw [← measuredInverseStepSources_eq r T] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredInverseStepSegments measuredInverseStepSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))))))))
  · intro cursor hh
    exact hInverseProgram_wellFormed n cursor r 256 T hh
  · intro cursor hh
    exact phaseInverseProgram_wellFormed n cursor r.phaseUpdate r.shiftEpoch hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .add true .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact coefficientInverseProgram_wellFormed n cursor (r.coefficient (certifiedActiveWindows 256 T).coefficient) (certifiedActiveWindows 256 T).coefficient.start (certifiedActiveWindows 256 T).coefficient.stop .sub false .work2 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .add false .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact intervalInverseProgram_wellFormed n cursor (r.remainder (certifiedActiveWindows 256 T).remainder) 256 (certifiedActiveWindows 256 T).remainder.start (certifiedActiveWindows 256 T).remainder.stop .sub true .work1 hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

attribute [local irreducible] measuredStepProgram measuredInverseStepProgram measuredIndexedStep measuredIndexedStepInverse

theorem measuredScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (width count first start : Nat)
    (h : (measuredIndexedSchedule r width first count).WellFormed) :
    (measuredScheduleProgram n r width count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (measuredStepProgram_wellFormed _ _ _ _ _ hs.1)
      (ih _ _ hs.2)

theorem measuredInverseScheduleProgram_wellFormed (n : Nat) (r : IndexedStepRegisters) (count first start : Nat)
    (h : (measuredIndexedScheduleInverse r 256 first count).WellFormed) :
    (measuredInverseScheduleProgram n r count first start).2.WellFormed := by
  induction count generalizing first start with
  | zero => trivial
  | succ count ih =>
    have hs := adaptive_seq_wellFormed_parts _ _ h
    exact appendCompiled_wellFormed _ _ (ih _ _ hs.1)
      (measuredInverseStepProgram_wellFormed _ _ _ _ hs.2)

attribute [local irreducible] measuredScheduleProgram measuredInverseScheduleProgram measuredIndexedSchedule measuredIndexedScheduleInverse

theorem measuredEEAForwardProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1MeasuredEEAForward r).WellFormed) : (measuredEEAForwardProgram n start r).2.WellFormed :=
  measuredScheduleProgram_wellFormed _ _ _ _ _ _ h

theorem measuredEEAReverseProgram_wellFormed (n start : Nat) (r : IndexedStepRegisters)
    (h : (secp256k1MeasuredEEAReverse r).WellFormed) : (measuredEEAReverseProgram n start r).2.WellFormed :=
  measuredInverseScheduleProgram_wellFormed _ _ _ _ _ h


attribute [local irreducible] measuredEEAForwardProgram measuredEEAReverseProgram preprocessProgram unpreprocessProgram productionParityProgram
  secp256k1MeasuredEEAForward secp256k1MeasuredEEAReverse eeaPreprocess eeaUnpreprocess secp256k1EEAParityCorrection

theorem measuredForwardWrapperProgram_wellFormed (n start : Nat) : (measuredForwardWrapperProgram n start).2.WellFormed := by
  have h := secp256k1MeasuredEEAForwardWrapper_wellFormed
  unfold measuredForwardWrapperProgram
  rw [← measuredForwardWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredForwardWrapperSegments measuredForwardWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact preprocessProgram_wellFormed n cursor
  · intro cursor hh
    exact measuredEEAForwardProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1

theorem measuredReverseWrapperProgram_wellFormed (n start : Nat) : (measuredReverseWrapperProgram n start).2.WellFormed := by
  have h := secp256k1MeasuredEEAReverseWrapper_wellFormed
  unfold measuredReverseWrapperProgram
  rw [← measuredReverseWrapperSources_eq ] at h
  apply sequenceProgram_wellFormed_of_source _ _ _ _ h
  unfold measuredReverseWrapperSegments measuredReverseWrapperSources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.nil)))))
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact productionParityProgram_wellFormed n cursor
  · intro cursor hh
    exact literalProgram_wellFormed _ hh.1
  · intro cursor hh
    exact measuredEEAReverseProgram_wellFormed n cursor indexedStepProductionRegisters hh
  · intro cursor hh
    exact unpreprocessProgram_wellFormed n cursor
theorem measuredForwardDataBankProgram_wellFormed (n start : Nat) :
    (measuredForwardDataBankProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2 (measuredForwardWrapperProgram_wellFormed n start)

theorem measuredReverseDataBankProgram_wellFormed (n start : Nat) :
    (measuredReverseDataBankProgram n start).2.WellFormed :=
  (relabelCompiled_wellFormed eeaWorkspaceExchange _).2 (measuredReverseWrapperProgram_wellFormed n start)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_MeasuredEEAPhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.SquarePhysical -/
section Port_SquarePhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem squareAddProgram_wellFormed (n start : Nat) (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=bits.length) (hnd : ([copied,c,r,t,f]++input++acc).Nodup)
    (hq : q∈input) : (squareAddProgram n start input acc bits p q copied c r t f).2.WellFormed := by
  have hqc : q≠copied := by
    intro he
    exact (List.nodup_cons.mp hnd).1 (by simp [← he,hq])
  have hg : CircuitWellFormed [.CX q copied] := by simp [CircuitWellFormed,Gate.WellFormed,hqc]
  exact prependCompiled_wellFormed _ _ hg
    (appendCompiled_wellFormed _ _
      (modularAddProgram_wellFormed n start input acc bits p copied c r t f hlen hne hk hnd)
      (literalProgram_wellFormed _ hg))

theorem squareSubProgram_wellFormed (n start : Nat) (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=bits.length) (hnd : ([copied,c,r,t,f]++input++acc).Nodup)
    (hq : q∈input) : (squareSubProgram n start input acc bits p q copied c r t f).2.WellFormed := by
  have hqc : q≠copied := by
    intro he
    exact (List.nodup_cons.mp hnd).1 (by simp [← he,hq])
  have hg : CircuitWellFormed [.CX q copied] := by simp [CircuitWellFormed,Gate.WellFormed,hqc]
  exact prependCompiled_wellFormed _ _ hg
    (appendCompiled_wellFormed _ _
      (modularSubProgram_wellFormed n start input acc bits p copied c r t f hlen hne hk hnd)
      (literalProgram_wellFormed _ hg))

attribute [local irreducible] squareAddProgram squareSubProgram

theorem squareProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcontrols : ∀ q∈controls,q∈input) :
    (squareProgram n start controls input (a::rest) bits p copied c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [squareProgram]
    apply appendCompiled_wellFormed
    · exact ih _ (fun z hz => hcontrols z (List.mem_cons_of_mem q hz))
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(squareProgram n start qs input (a::rest) bits p copied c r t f).1)
          (start+(squareProgram n start qs input (a::rest) bits p copied c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · exact squareAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
          hnd (hcontrols q (by simp))
      · apply appendCompiled_wellFormed
        · exact modularDoubleProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout [] input (a::rest) c r t f (List.nodup_cons.mp hnd).2)
        · exact squareAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
            hnd (hcontrols q (by simp))

theorem squareInverseProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcontrols : ∀ q∈controls,q∈input) :
    (squareInverseProgram n start controls input (a::rest) bits p copied c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [squareInverseProgram]
    apply appendCompiled_wellFormed
    · exact squareSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
        hnd (hcontrols q (by simp))
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(squareSubProgram n start input (a::rest) bits p q copied c r t f).1)
          (start+(squareSubProgram n start input (a::rest) bits p q copied c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · trivial
      · apply appendCompiled_wellFormed
        · exact modularHalveProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout [] input (a::rest) c r t f (List.nodup_cons.mp hnd).2)
        · exact ih _ (fun z hz => hcontrols z (List.mem_cons_of_mem q hz))
attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_wellFormed (n start : Nat) (x y : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (q copied c r t f : Wire)
    (hxlen : x.length=(a::rest).length) (hylen : y.length=(a::rest).length)
    (hk : (a::rest).length=correction.length) (hm : (a::rest).length=modulus.length)
    (hsq : ([copied,c,r,t,f]++y++(a::rest)).Nodup)
    (hsub : ([q,copied,f,r,c]++(a::rest)++x).Nodup) :
    (squareSubtractProgram n start x y (a::rest) correction modulus p q copied c r t f).2.WellFormed := by
  unfold squareSubtractProgram
  apply appendCompiled_wellFormed
  · exact squareProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hylen hk hsq (fun _ h => h)
  · apply appendCompiled_wellFormed
    · exact modularSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hxlen.symm
        (by rw [hxlen]; simp) (hxlen.trans hm) hsub
    · exact squareInverseProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ _ _ hylen hm hsq (fun _ h => h)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_SquarePhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.InPlacePhysical -/
section Port_InPlacePhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
private theorem port_InPlacePhysical_figure15_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 580 256 ++ List.range' 7 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

private theorem port_InPlacePhysical_figure15_data_layout :
    ([558,560,561,559] ++ List.range' 263 256 ++ List.range' 7 256 ++ List.range' 580 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega


attribute [local irreducible] hornerProgram hornerInverseProgram

theorem multiplyWorkProgram_wellFormed (n start : Nat) : (multiplyWorkProgram n start).2.WellFormed := by
  have ha : List.range' 7 256 = 7 :: List.range' 8 255 := rfl
  unfold multiplyWorkProgram
  rw [ha]
  apply hornerProgram_wellFormed
  · simp
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact port_InPlacePhysical_figure15_layout

theorem multiplyDataProgram_wellFormed (n start : Nat) : (multiplyDataProgram n start).2.WellFormed := by
  have ha : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold multiplyDataProgram
  rw [ha]
  apply hornerProgram_wellFormed
  · simp
  · simp [secp256k1ReductionConstantBits]
  · rw [← ha]; exact port_InPlacePhysical_figure15_data_layout

theorem unmultiplyDataProgram_wellFormed (n start : Nat) : (unmultiplyDataProgram n start).2.WellFormed := by
  have ha : List.range' 580 256 = 580 :: List.range' 581 255 := rfl
  unfold unmultiplyDataProgram
  rw [ha]
  apply hornerInverseProgram_wellFormed
  · simp
  · simp only [List.length_cons, List.length_range', constantBits_length]
  · rw [← ha]; exact port_InPlacePhysical_figure15_data_layout
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_InPlacePhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.InPlaceCompletePhysical -/
section Port_InPlaceCompletePhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem correctionCompiled_wellFormed (n start : Nat) (ws : List Wire) (prior : List (Fin start)) :
    (correctionCompiled n start ws prior).2.WellFormed :=
  registerCorrectionProgram_wellFormed _ _ _ trivial

theorem appendLiteral_wellFormed {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (gs : Circuit) (hp : p.2.WellFormed) (hg : CircuitWellFormed gs) :
    (appendLiteral p gs).2.WellFormed :=
  appendCompiled_wellFormed _ _ hp (literalProgram_wellFormed _ hg)

theorem collectProgram_wellFormed (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (hn : ∀ cursor prior, (next cursor prior).2.WellFormed)
    (ws : List Wire) (start : Nat) (prior : List (Fin start)) :
    (collectProgram n next ws start prior).2.WellFormed := by
  induction ws generalizing start with
  | nil => exact hn _ _
  | cons w ws ih => simpa only [collectProgram,castFinish_wellFormed,Straight.WellFormed] using ih (start+1) _

theorem appendRetaining_wellFormed {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count))
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (prior : List (Fin start)) (hp : p.2.WellFormed)
    (hn : ∀ cursor prior, (next cursor prior).2.WellFormed) :
    (appendRetaining p next prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ hp (hn _ _)

private theorem port_InPlaceCompletePhysical_swapOutput_wellFormed : CircuitWellFormed fig15SwapOutput := by
  intro g hg
  simp only [fig15SwapOutput,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hg
  obtain ⟨i,hi,hg⟩ := hg
  rcases hg with rfl | rfl | rfl <;> simp [Gate.WellFormed]

attribute [local irreducible] multiplyWorkProgram multiplyDataProgram unmultiplyDataProgram
  measuredForwardWrapperProgram measuredReverseWrapperProgram measuredForwardDataBankProgram measuredReverseDataBankProgram

theorem divisionCleanupProgram_wellFormed (n start : Nat) : (divisionCleanupProgram n start).2.WellFormed :=
  appendLiteral_wellFormed _ _ (unmultiplyDataProgram_wellFormed _ _) port_InPlaceCompletePhysical_swapOutput_wellFormed

theorem multiplicationCleanupProgram_wellFormed (n start : Nat) : (multiplicationCleanupProgram n start).2.WellFormed := by
  unfold multiplicationCleanupProgram
  exact appendCompiled_wellFormed _ _ (unmultiplyDataProgram_wellFormed _ _)
    (appendLiteral_wellFormed _ _ (measuredReverseDataBankProgram_wellFormed _ _) port_InPlaceCompletePhysical_swapOutput_wellFormed)

attribute [local irreducible] divisionCleanupProgram multiplicationCleanupProgram
theorem divisionCorrectionProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (divisionCorrectionProgram n start prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ (correctionCompiled_wellFormed _ _ _ _) (divisionCleanupProgram_wellFormed _ _)

theorem divisionAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (divisionAfterResetProgram n start prior).2.WellFormed := by
  unfold divisionAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredReverseDataBankProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact divisionCorrectionProgram_wellFormed n

theorem multiplicationCorrectionProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (multiplicationCorrectionProgram n start prior).2.WellFormed :=
  appendCompiled_wellFormed _ _ (correctionCompiled_wellFormed _ _ _ _) (multiplicationCleanupProgram_wellFormed _ _)

theorem multiplicationAfterResetProgram_wellFormed (n start : Nat) (prior : List (Fin start)) :
    (multiplicationAfterResetProgram n start prior).2.WellFormed := by
  unfold multiplicationAfterResetProgram
  apply appendRetaining_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredForwardDataBankProgram_wellFormed _ _) (multiplyDataProgram_wellFormed _ _)
  · exact multiplicationCorrectionProgram_wellFormed n

attribute [local irreducible] divisionAfterResetProgram multiplicationAfterResetProgram collectProgram
theorem divisionProgram_wellFormed (n start : Nat) : (divisionProgram n start).2.WellFormed := by
  unfold divisionProgram
  apply appendCompiled_wellFormed
  · exact appendCompiled_wellFormed _ _ (measuredForwardWrapperProgram_wellFormed _ _) (multiplyWorkProgram_wellFormed _ _)
  · exact collectProgram_wellFormed _ _ (divisionAfterResetProgram_wellFormed n) _ _ _

theorem multiplicationProgram_wellFormed (n start : Nat) : (multiplicationProgram n start).2.WellFormed := by
  unfold multiplicationProgram
  exact appendCompiled_wellFormed _ _ (multiplyWorkProgram_wellFormed _ _)
    (collectProgram_wellFormed _ _ (multiplicationAfterResetProgram_wellFormed n) _ _ _)
attribute [local irreducible] divisionProgram multiplicationProgram
theorem zeroDivisionProgram_wellFormed (n start : Nat) : (zeroDivisionProgram n start).2.WellFormed :=
  surroundCompiled_wellFormed _ _ _ fig15ZeroPrepare_wellFormed fig15ZeroRestore_wellFormed (divisionProgram_wellFormed _ _)

theorem zeroMultiplicationProgram_wellFormed (n start : Nat) : (zeroMultiplicationProgram n start).2.WellFormed :=
  surroundCompiled_wellFormed _ _ _ fig15ZeroPrepare_wellFormed fig15ZeroRestore_wellFormed (multiplicationProgram_wellFormed _ _)

attribute [local irreducible] squareSubtractProgram

theorem pointSquareProgram_wellFormed (n start : Nat) : (pointSquareProgram n start).2.WellFormed := by
  unfold pointSquareProgram
  apply squareSubtractProgram_wellFormed
  · simp
  · simp
  · simp [secp256k1ReductionConstantBits]
  · simp
  all_goals
    have hw : 7 :: List.range' 8 255 = List.range' 7 256 := rfl
    rw [hw]
    simp only [List.nodup_append]
    refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
    all_goals
      intro a ha b hb he
      subst a
      simp at ha hb
      rcases ha with h | h | h | h | h
      all_goals first | omega | (rcases h with rfl | ⟨hl,hu⟩ <;> omega)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_InPlaceCompletePhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.CoordinatePhysical -/
section Port_CoordinatePhysical

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

theorem fieldLoadOps_physical (field : PointField) : ∀ op ∈ fieldLoadOps field, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [fieldLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    simp only [List.mem_range'] at ht
    simp only [List.mem_cons,pointLookupPath,List.mem_range'] at hc
    change control ≠ target
    rcases hc with rfl | hc
    all_goals intro he; subst target; omega

theorem fieldLoadProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLoadProgram field start).WellFormed := by
  unfold fieldLoadProgram
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ (fieldLoadOps_physical field) _

attribute [local irreducible] fieldLoadProgram modularAddProgram appendCompiled

theorem fieldLookupAddProgram_wellFormed (field : PointField) (acc : List Wire) (start : Nat)
    (hl : acc.length = 256) (hn : ([836,559,560,561,558] ++ List.range' 7 256 ++ acc).Nodup) :
    (fieldLookupAddProgram field acc start).2.WellFormed := by
  let add := modularAddProgram 32768 (start+32767) (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
  have ha : add.2.WellFormed := modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _
    (by simpa using hl.symm) (by omega) (by simp [hl,secp256k1ReductionConstantBits]) hn
  exact appendCompiled_wellFormed ⟨32767,fieldLoadProgram field start⟩
    (appendCompiled add ⟨32767,fieldLoadProgram field (start+32767+add.1)⟩)
    (fieldLoadProgram_wellFormed _ _)
    (appendCompiled_wellFormed add ⟨32767,fieldLoadProgram field (start+32767+add.1)⟩ ha (fieldLoadProgram_wellFormed _ _))
private theorem port_CoordinatePhysical_fieldAccumulator_layout (base : Nat) (hb : base=263 ∨ base=580) :
    ([836,559,560,561,558] ++ List.range' 7 256 ++ List.range' base 256).Nodup := by
  rcases hb with rfl | rfl
  all_goals
    simp only [List.nodup_append]
    refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
    all_goals
      intro a ha b hb he
      subst a
      simp at ha hb
      rcases ha with h | h | h | h | h
      all_goals omega

theorem fieldLookupXProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLookupAddProgram field (List.range' 263 256) start).2.WellFormed :=
  fieldLookupAddProgram_wellFormed _ _ _ (by simp) (port_CoordinatePhysical_fieldAccumulator_layout _ (Or.inl rfl))

theorem fieldLookupYProgram_wellFormed (field : PointField) (start : Nat) :
    (fieldLookupAddProgram field (List.range' 580 256) start).2.WellFormed :=
  fieldLookupAddProgram_wellFormed _ _ _ (by simp) (port_CoordinatePhysical_fieldAccumulator_layout _ (Or.inr rfl))

attribute [local irreducible] fieldLookupAddProgram yNegateProgram

theorem signedFieldProgram_wellFormed (field : PointField) (start : Nat) :
    (signedFieldProgram field start).2.WellFormed := by
  unfold signedFieldProgram
  exact appendCompiled_wellFormed _ _ (yNegateProgram_wellFormed _)
    (appendCompiled_wellFormed _ _ (fieldLookupYProgram_wellFormed _ _) (yNegateProgram_wellFormed _))

attribute [local irreducible] zeroDivisionProgram zeroMultiplicationProgram pointSquareProgram signedFieldProgram xNegateProgram

theorem coordinateProgram_wellFormed (start : Nat) : (coordinateProgram start).2.WellFormed := by
  unfold coordinateProgram
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [coordinateSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
  · exact zeroDivisionProgram_wellFormed _ _
  · exact pointSquareProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact zeroMultiplicationProgram_wellFormed _ _
  · exact xNegateProgram_wellFormed _ _
  · exact fieldLookupXProgram_wellFormed _ _
  · exact signedFieldProgram_wellFormed _ _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_CoordinatePhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ActualPhysical -/
section Port_ActualPhysical

/-! Physical validity of the actual first and signed windows and their outer composition. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
attribute [local irreducible] coordinateProgram

theorem sharedCoordinateProgram_wellFormed (w : OddWindow) (start : Nat) :
    (sharedCoordinateProgram w start).2.WellFormed :=
  (reindexCompiled_wellFormed _ _).mpr (coordinateProgram_wellFormed start)

attribute [local irreducible] sharedCoordinateProgram sharedYNegateProgram placedBatchProgram

theorem batchedWindowCore_wellFormed (w : OddWindow) (start : Nat) :
    (batchedWindowCore w start).2.WellFormed := by
  apply sequenceProgram_wellFormed
  intro p hp cursor
  simp only [batchedWindowSegments,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact sharedCoordinateProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _
  · exact placedBatchProgram_wellFormed _ _
  · exact sharedYNegateProgram_wellFormed _ _

attribute [local irreducible] batchedWindowCore

theorem batchedWindowPrepared_wellFormed (w : OddWindow) (start : Nat) :
    (batchedWindowPrepared w start).2.WellFormed := by
  exact surroundCompiled_wellFormed _ _ _
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (signedAddressCircuit_wellFormed _ _ _ (by decide) (by decide))
    (batchedWindowCore_wellFormed w start)

attribute [local irreducible] batchedWindowPrepared

theorem actualBatchedWindow_wellFormed (w : OddWindow) (start : Nat) :
    ((actualBatchedWindow w).program start).WellFormed := by
  apply shiftStraight_wellFormed
  exact (relabelStraight_wellFormed _ _).mpr (batchedWindowPrepared_wellFormed w 0)

theorem firstLookupOps_physical : ∀ op ∈ firstLookupOps, op.Physical := by
  apply unaryLookupOps_physical
  · exact tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)
  · intro label control hc g hg
    simp only [pointLeaf,lookupLeafGates,List.mem_map] at hg
    obtain ⟨⟨ref,target⟩,hm,rfl⟩ := hg
    have ht := (List.of_mem_zip hm).2
    change control ≠ target
    have hn : ∀ c ∈ 836 :: List.range' 519 16, c ∉ pointLogicalWires := by
      intro c hc ht
      simp only [List.mem_cons,List.mem_range'] at hc
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
        List.mem_range',List.mem_singleton] at ht
      rcases hc with rfl | hc
      all_goals omega
    exact fun he => hn control hc (he ▸ ht)

theorem firstLookupProgram_wellFormed (start : Nat) : (firstLookupProgram start).WellFormed := by
  unfold firstLookupProgram
  rw [castFinish_wellFormed]
  exact lookupProgram_wellFormed _ firstLookupOps_physical _

attribute [local irreducible] firstLookupProgram

theorem actualFirstWindow_wellFormed (start : Nat) :
    (actualFirstWindow.program start).WellFormed :=
  (reindexStraight_wellFormed _ _).mpr (firstLookupProgram_wellFormed start)

attribute [local irreducible] actualBatchedWindow actualFirstWindow

theorem batchedOuterPlan_windowsWellFormed : batchedOuterPlan.WindowsWellFormed := by
  intro w hw start
  change w ∈ actualLeftWindows ++ actualRightWindows at hw
  simp only [actualLeftWindows,actualRightWindows,List.mem_append,List.mem_cons,List.mem_ofFn] at hw
  rcases hw with (rfl | ⟨k,rfl⟩) | ⟨k,rfl⟩
  · exact actualFirstWindow_wellFormed _
  · exact actualBatchedWindow_wellFormed _ _
  · exact actualBatchedWindow_wellFormed _ _

attribute [local irreducible] batchedOuterPlan

theorem batchedOuterPlan_round_wellFormed (start : Nat) :
    (batchedOuterPlan.round start).WellFormed :=
  batchedOuterPlan.round_wellFormed batchedOuterPlan_windowsWellFormed start

theorem batchedOuterPlan_repeat_wellFormed (count start : Nat) :
    (batchedOuterPlan.repeat count start).WellFormed :=
  batchedOuterPlan.repeat_wellFormed batchedOuterPlan_windowsWellFormed count start

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ActualPhysical

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.HistoryExecution -/
section Port_HistoryExecution

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def historyAfter {s : Nat} (e : Nat) (history : Fin s → Bool) (bits : List Bool) : Fin e → Bool :=
  fun i => (List.ofFn history ++ bits).getD i.val false

theorem historyAfter_nil {s : Nat} (history : Fin s → Bool) : historyAfter s history List.nil = history := by
  funext i
  simp [historyAfter, i.isLt]

theorem historyAfter_cons {s e : Nat} (history : Fin s → Bool) (v : Bool) (bits : List Bool) :
    historyAfter e (Fin.lastCases v history) bits = historyAfter e history (v :: bits) := by
  funext i
  simp only [historyAfter,List.ofFn_succ',Fin.lastCases_castSucc,Fin.lastCases_last,
    List.concat_eq_append,List.append_assoc,List.singleton_append]

/-- Exact ordered branch composition, including the records supplied to the suffix. -/
theorem straight_append_run_history {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    ((p.append q).instantiate read history).run =
      (p.instantiate read history).run.flatMap (fun b =>
        (q.instantiate read (historyAfter m history b.history)).run.map (fun c => b.seq c)) := by
  induction p with
  | done =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,List.flatMap_cons,List.flatMap_nil,List.append_nil,historyAfter_nil]
    simp [InstrumentBranch.seq]
  | gate g p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    rfl
  | recordGate i v g p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    rfl
  | measure w p ih =>
    simp only [Straight.append,Straight.instantiate,AdaptiveCircuit.run,ih,
      List.map_flatMap,List.flatMap_map,List.map_map,List.flatMap_append,Function.comp_def]
    simp only [historyAfter_cons]
    rfl
theorem historyAfter_old {s e : Nat} (history : Fin s → Bool) (bits : List Bool)
    (i : Fin e) (hi : i.val < s) : historyAfter e history bits i = history ⟨i.val,hi⟩ := by
  unfold historyAfter
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [hi]

theorem historyAfter_new {s e : Nat} (history : Fin s → Bool) (bits : List Bool)
    (i : Fin e) (hi : s ≤ i.val) : historyAfter e history bits i = bits.getD (i.val-s) false := by
  unfold historyAfter
  rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
  simp

/-- The Fourier suffix sees the exact new outcomes, not arithmetic-cleanup records. -/
theorem nextBankPrior_map_historyAfter {s : Nat} (count : Nat) (prior : List (Fin s))
    (history : Fin (s+count) → Bool) (bits : List Bool) (hl : bits.length = 16) :
    (nextBankPrior count prior).map (historyAfter (s+count+16) history bits) =
      bits.reverse ++ prior.map (fun i => history ⟨i.val,by omega⟩) := by
  simp only [nextBankPrior,List.map_append,List.map_reverse,List.map_ofFn,List.map_map]
  congr 1
  · congr 1
    have he : List.ofFn (fun i : Fin 16 => bits.getD i.val false) = bits := by
      apply List.ext_getElem
      · simpa using hl.symm
      · intro i hi hj
        simp only [List.getElem_ofFn]
        exact List.getD_eq_getElem _ false hj
    apply Eq.trans _ he
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_def]
    rw [historyAfter_new _ _ _ (by simp)]
    simp
  · apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    exact historyAfter_old _ _ _ (by simpa using Nat.lt_add_right count i.isLt)

/-- The complete ordered instrument of a Fourier bank followed by any straight suffix. -/
theorem fourierProgram_append_run_history {n e : Nat} (dir : PhaseDir) (ws : List Wire)
    (start : Nat) (prior : List (Fin start)) (q : Straight n (start+ws.length) e)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (((fourierProgram n dir ws start prior).append q).instantiate read history).run =
      (fourierOutcomes ws.length).flatMap (fun bits =>
        (q.instantiate read (historyAfter (start+ws.length) history bits)).run.map
          (fun b => InstrumentBranch.seq ⟨bits,fourierBranch dir ws (prior.map history) bits⟩ b)) := by
  rw [straight_append_run_history,fourierProgram_run,semiclassicalFourier_run,List.flatMap_map]
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_HistoryExecution

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.OuterExecution -/
section Port_OuterExecution

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

noncomputable def sourceOuterAxis (wires : List Wire) : List AdaptiveCircuit → List Bool → AdaptiveCircuit
  | [], _ => .done
  | call :: calls, prior => .unitary (wires.reverse.map Gate.H)
      (call.seq (fourierContinue .inverse wires prior (sourceOuterAxis wires calls)))

theorem prepareOuterBank_append_run {n s m e : Nat} (wires : List Wire)
    (p : Straight n s m) (q : Straight n m e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (((prepareOuterBank wires p).append q).instantiate read history).run =
      (AdaptiveCircuit.unitary (wires.map Gate.H) ((p.append q).instantiate read history)).run := by
  induction wires with
  | nil =>
    simp only [prepareOuterBank,List.foldr_nil,List.map_nil,AdaptiveCircuit.run]
    change _ = List.map (fun a => a) _
    rw [List.map_id']
  | cons w ws ih =>
    simp only [prepareOuterBank,List.foldr_cons,Straight.append,Straight.instantiate,
      TemplateGate.instantiate,AdaptiveCircuit.run,List.map_cons]
    rw [show (((ws.foldr (fun w p => Straight.gate (.literal (.H w)) p) p).append q).instantiate read history).run =
      (AdaptiveCircuit.unitary (ws.map Gate.H) ((p.append q).instantiate read history)).run from ih]
    simp only [AdaptiveCircuit.run,List.map_map]
    apply List.map_congr_left
    intro a ha
    cases a
    rfl

theorem bankPrior_map_historyAfter {s : Nat} (count : Nat) (prior : List (Fin s))
    (history : Fin s → Bool) (bits : List Bool) :
    (bankPrior count prior).map (historyAfter (s+count) history bits) = prior.map history := by
  simp only [bankPrior,List.map_map]
  apply List.map_congr_left
  intro i hi
  exact historyAfter_old _ _ _ i.isLt

theorem fourierBank_append_run {n e : Nat} (wires : Vector Wire 16) (start : Nat)
    (prior : List (Fin start)) (q : Straight n (start+16) e)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (((castFinish (by simp) (fourierProgram n .inverse wires.toList start prior)).append q).instantiate read history).run =
      (fourierOutcomes 16).flatMap (fun bits =>
        (q.instantiate read (historyAfter (start+16) history bits)).run.map
          (fun b => InstrumentBranch.seq ⟨bits,fourierBranch .inverse wires.toList (prior.map history) bits⟩ b)) := by
  rw [straight_append_run_history,castFinish_instantiate,fourierProgram_run,semiclassicalFourier_run,List.flatMap_map]
  simp

attribute [local irreducible] fourierProgram prepareOuterBank

theorem outerAxis_run {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (calls : List AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hc : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) ws calls)
    (start : Nat) (prior : List (Fin start)) (history : Fin start → Bool) :
    ((outerAxis wires ws start prior).instantiate read history).run =
      (sourceOuterAxis wires.toList calls (prior.map history)).run := by
  induction hc generalizing start with
  | nil => rfl
  | @cons w call ws calls hw hws ih =>
    simp only [outerAxis,castFinish_instantiate,prepareOuterBank_append_run,sourceOuterAxis,AdaptiveCircuit.run]
    congr 1
    rw [straight_append_run_history,hw]
    rw [AdaptiveCircuit.run_seq]
    unfold Instrument.seq
    apply List.flatMap_congr
    intro a ha
    rw [fourierBank_append_run]
    simp only [fourierContinue_run,Vector.length_toList]
    congr 1
    apply List.flatMap_congr
    intro bits hb
    rw [ih]
    rw [nextBankPrior_map_historyAfter _ _ _ _ ((fourierOutcomes_mem _ _).mp hb)]
    rw [bankPrior_map_historyAfter]
    have ho : prior.map (fun i => historyAfter (start+w.count) history a.history ⟨i.val,by omega⟩) = prior.map history := by
      apply List.map_congr_left
      intro i hi
      exact historyAfter_old _ _ _ i.isLt
    rw [ho]
noncomputable def sourceOuterRound (wires : List Wire) (left right : List AdaptiveCircuit)
    (reset : List Wire) : AdaptiveCircuit :=
  .unitary [.X 836] ((sourceOuterAxis wires left List.nil).seq
    ((sourceOuterAxis wires right List.nil).seq
      (.unitary [.X 836] (measureResetWithCorrection reset (fun _ => [])))))

theorem outerPlan_round_run {n : Nat} (p : OuterPlan n) (left right : List AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hl : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) p.left.toList left)
    (hr : List.Forall₂ (fun w c => ∀ start history, ((w.program start).instantiate read history).run = c.run) p.right.toList right)
    (start : Nat) (history : Fin start → Bool) :
    ((p.round start).instantiate read history).run = (sourceOuterRound p.wires.toList left right p.reset).run := by
  have htail (cursor : Nat) (history : Fin cursor → Bool) :
      ((Straight.gate (.literal (.X 836)) (resetProgram n cursor p.reset)).instantiate read history).run =
        (AdaptiveCircuit.unitary [.X 836] (measureResetWithCorrection p.reset (fun _ => []))).run := by
    simp only [Straight.instantiate,TemplateGate.instantiate,AdaptiveCircuit.run,resetProgram_run]
  have hright (cursor : Nat) (history : Fin cursor → Bool) :
      (((outerAxis p.wires p.right.toList cursor List.nil).append
        (.gate (.literal (.X 836)) (resetProgram n (cursor+axisCount p.right.toList) p.reset))).instantiate read history).run =
        ((sourceOuterAxis p.wires.toList right List.nil).seq
          (.unitary [.X 836] (measureResetWithCorrection p.reset (fun _ => [])))).run := by
    rw [append_run_fixed _ _ _ _ _ (htail _),AdaptiveCircuit.run_seq,outerAxis_run _ _ _ _ hr]
    simp only [List.map_nil,AdaptiveCircuit.run_seq]
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,TemplateGate.instantiate,sourceOuterRound,AdaptiveCircuit.run]
  congr 1
  rw [append_run_fixed _ _ _ _ _ (hright _),AdaptiveCircuit.run_seq,outerAxis_run _ _ _ _ hl]
  simp only [List.map_nil,AdaptiveCircuit.run_seq]

theorem outerPlan_repeat_run {n : Nat} (p : OuterPlan n) (source : AdaptiveCircuit)
    (read : ConstantBit n → Bool)
    (hround : ∀ start history, ((p.round start).instantiate read history).run = source.run)
    (count start : Nat) (history : Fin start → Bool) :
    ((p.repeat count start).instantiate read history).run = (repeatWindowProgram source count).run := by
  induction count generalizing start with
  | zero => simp only [OuterPlan.repeat,castFinish_instantiate,repeatWindowProgram,Straight.instantiate]
  | succ k ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate,repeatWindowProgram]
    rw [append_run_fixed _ _ _ _ _ (ih _),AdaptiveCircuit.run_seq,hround,← AdaptiveCircuit.run_seq]

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_OuterExecution

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ActualExecution -/
section Port_ActualExecution

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

noncomputable def actualFirstSource (Q : Point) : AdaptiveCircuit :=
  physicalPointLookup (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • G))
noncomputable def actualOddSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide))
noncomputable def actualLeftSources (Q : Point) : List AdaptiveCircuit :=
  actualFirstSource Q :: List.ofFn (fun k : Fin 15 => actualOddSource Q (.left ⟨14-k.val,by omega⟩))
noncomputable def actualRightSources (Q : Point) : List AdaptiveCircuit :=
  List.ofFn (fun k : Fin 13 => actualOddSource Q (.right ⟨12-k.val,by omega⟩))
noncomputable def actualRoundSource (Q : Point) : AdaptiveCircuit :=
  sourceOuterRound streamAddress.reverse (actualLeftSources Q) (actualRightSources Q) batchedResetWires

private theorem port_ActualExecution_forall₂_ofFn {α β : Type} (R : α → β → Prop) {n : Nat}
    (a : Fin n → α) (b : Fin n → β) (h : ∀ i, R (a i) (b i)) : List.Forall₂ R (List.ofFn a) (List.ofFn b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

theorem actualLeftSources_run (Q : Point) (hQ : order • Q=0) :
    List.Forall₂ (fun w c => ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).run = c.run)
      actualLeftWindows (actualLeftSources Q) := by
  apply List.Forall₂.cons
  · exact fun start history => actualFirstWindow_run start Q hQ history
  · apply port_ActualExecution_forall₂_ofFn
    intro k start history
    exact actualBatchedWindow_run _ start Q hQ history

theorem actualRightSources_run (Q : Point) (hQ : order • Q=0) :
    List.Forall₂ (fun w c => ∀ start history,
      ((w.program start).instantiate (readConstant coefficientAt Q) history).run = c.run)
      actualRightWindows (actualRightSources Q) := by
  apply port_ActualExecution_forall₂_ofFn
  intro k start history
  exact actualBatchedWindow_run _ start Q hQ history

attribute [local irreducible] actualLeftWindows actualRightWindows actualLeftSources actualRightSources

theorem batchedOuterPlan_round_run (Q : Point) (hQ : order • Q=0) (start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.round start).instantiate (readConstant coefficientAt Q) history).run =
      (actualRoundSource Q).run := by
  exact outerPlan_round_run batchedOuterPlan _ _ _ (actualLeftSources_run Q hQ) (actualRightSources_run Q hQ) start history

attribute [local irreducible] batchedOuterPlan actualRoundSource

theorem batchedOuterPlan_repeat_run (Q : Point) (hQ : order • Q=0) (count start : Nat) (history : Fin start → Bool) :
    ((batchedOuterPlan.repeat count start).instantiate (readConstant coefficientAt Q) history).run =
      (repeatWindowProgram (actualRoundSource Q) count).run :=
  outerPlan_repeat_run _ _ _ (batchedOuterPlan_round_run Q hQ) count start history

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ActualExecution

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.Rounds -/
section Port_Rounds

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- Shared repetition count for the entry, decoder, resource and success proofs. -/
def streamingRounds : Nat := 26

def OuterPlan.entryForStreaming (coefficients : List PointCoeff)
    (p : OuterPlan coefficients.length) : StraightEntry :=
  ⟨coefficients, streamingRounds*p.stride,
    castFinish (by omega) (p.repeat streamingRounds 0)⟩

def OuterPlan.positionsForStreaming {n : Nat} (p : OuterPlan n)
    (r : Fin streamingRounds) : TrialPositions legacyDecoderParams where
  left := ⟨(axisPositions p.left.toList (r.val*p.stride)).toArray,
    by simp [axisPositions_length, legacyDecoderParams]⟩
  right := ⟨(axisPositions p.right.toList (r.val*p.stride+axisCount p.left.toList)).toArray,
    by simp [axisPositions_length, legacyDecoderParams]⟩

def OuterPlan.layoutForStreaming {n : Nat} (p : OuterPlan n) : DecodeLayout :=
  ⟨.wrappedShift, legacyDecoderParams, List.ofFn p.positionsForStreaming,
    by simp [streamingRounds]⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_Rounds

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.ActualWindow -/
section Port_ActualWindow

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Secp256k1 ShorECDLP.Challenge
private theorem port_ActualWindow_parkedWindow_valid (start : Nat) (hs : 855≤start) (s : BasisState)
    (hv : PointLookupValid s) : PointLookupValid (relabelBasis (windowAddressPerm start hs).symm s) := by
  have he (w : Wire) (hw : w<839) : relabelBasis (windowAddressPerm start hs).symm s w=s w := by
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w hw]
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro w hw
    have hb : w<839 := by simp only [List.mem_append,List.mem_range'_1] at hw; (try dsimp only [Wire] at *); omega
    rw [he w hb]
    exact hv.1.1 w hw
  · rw [he 837 (by decide)]; exact hv.1.2.1
  · have hh : wireValues (List.range' 263 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 263 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.1
  · have hh : wireValues (List.range' 580 256) (relabelBasis (windowAddressPerm start hs).symm s)=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      apply he w
      simp only [List.mem_range'_1] at hw
      (try dsimp only [Wire] at *); omega
    rw [hh]; exact hv.1.2.2.2
  · rw [he 836 (by decide)]; exact hv.2

private theorem port_ActualWindow_point_bank_bound (w : Wire) (hw : w∈pointLogicalWires) : w<839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega
private theorem port_ActualWindow_relabel_pointWrite (start : Nat) (hs : 855≤start)
    (P : ShorECDLP.Secp256k1.Point) (s : BasisState) :
    relabelBasis (windowAddressPerm start hs)
      (pointWrite P (relabelBasis (windowAddressPerm start hs).symm s))=pointWrite P s := by
  have hsym : (windowAddressPerm start hs).symm=windowAddressPerm start hs := rfl
  funext w
  by_cases hw : w∈pointLogicalWires
  · have he := windowAddressPerm_core start hs w (port_ActualWindow_point_bank_bound w hw)
    simp [relabelBasis,hsym,he,pointWrite,hw]
  · have hn : (windowAddressPerm start hs).symm w∉pointLogicalWires := by
      intro h
      have he := windowAddressPerm_core start hs _ (port_ActualWindow_point_bank_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp [relabelBasis,pointWrite,hw,hn]

private theorem port_ActualWindow_relabel_coordinates (start : Nat) (hs : 855≤start) (s : BasisState) :
    pointStateCoordinates (relabelBasis (windowAddressPerm start hs).symm s)=pointStateCoordinates s := by
  have he (bits : List Wire) (hb : ∀ w∈bits,w<839) :
      wireValues bits (relabelBasis (windowAddressPerm start hs).symm s)=wireValues bits s := by
    apply List.map_congr_left
    intro w hw
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w (hb w hw)]
  have hx := he (List.range' 263 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  have hy := he (List.range' 580 256) (by intro w hw; simp only [List.mem_range'_1] at hw; dsimp only [Wire] at *; omega)
  simp only [pointStateCoordinates,hx,hy,relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs 838 (by decide)]


theorem windowAddressPerm_workspace (w : Wire) (hw : w ∈ batchWorkspace) :
    windowAddressPerm 855 (by decide) w=w := by
  change windowAddressSwap 855 w=w
  simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hw
  unfold windowAddressSwap
  split_ifs <;> (try dsimp only [Wire] at *) <;> omega

theorem actualWindow_pullback_ready (s : BasisState) (hs : BatchedPointReady s) :
    BatchedPointReady (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  refine ⟨port_ActualWindow_parkedWindow_valid 855 (by decide) s hs.1,?_⟩
  intro w hw
  change s (windowAddressPerm 855 (by decide) w)=false
  rw [windowAddressPerm_workspace w hw]
  exact hs.2 w hw

theorem actualWindow_pullback_valid (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (relabelBasis (windowAddressPerm 855 (by decide)).symm s) := by
  obtain ⟨hs,P,hP⟩ := hs
  exact ⟨actualWindow_pullback_ready s hs,P,(port_ActualWindow_relabel_coordinates 855 (by decide) s).trans hP⟩

noncomputable def actualBatchedWindowState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (preparedBatchState Q w (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

theorem actualBatchedWindow_coherent (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn (((actualBatchedWindow w).program start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
  have h := (batchedWindowPreparedSource_coherent Q hQ hn w).relabel (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn ((batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (preparedBatchState Q w)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm))) BatchedWindowValid := by
    obtain ⟨cs,hc,hm⟩ := h
    exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (actualWindow_pullback_valid s hs)),hm⟩
  have he : CoherentlyImplementsOn ((batchedWindowPreparedSource Q w).relabel (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w)) BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [actualBatchedWindowState,LinearMap.comp_apply,relabelState,ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [actualBatchedWindow_run w start Q hQ history]
  exact he

theorem actualBatchedWindowState_correct (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))
        else -windowPoint Q w (tableAddressValue pointLookupAddress
          (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s)))) s := by
  unfold actualBatchedWindowState
  rw [preparedBatchState_correct Q hQ hn w _ (actualWindow_pullback_ready s hs) P
    ((port_ActualWindow_relabel_coordinates 855 (by decide) s).trans hP),port_ActualWindow_relabel_pointWrite]
  have he : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    simp only [relabelBasis,Equiv.symm_symm]
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [he]

private theorem port_ActualWindow_address_word_eq (bits : List Wire) (s : BasisState) :
    tableAddressValue bits s=boolWordToNat (wireValues bits s) := by
  induction bits with
  | nil => rfl
  | cons w ws ih => simpa only [tableAddressValue,wireValues,List.map_cons,boolWordToNat] using congrArg (fun n => (s w).toNat+2*n) ih

theorem actualWindow_selected_address (s : BasisState) (hs : BatchedPointReady s) :
    tableAddressValue pointLookupAddress
      (batchPrepareState (relabelBasis (windowAddressPerm 855 (by decide)).symm s))=
      signedTableAddress 32768 (windowRawDigit 0 s) := by
  have hq : relabelBasis (windowAddressPerm 855 (by decide)).symm s 836=true :=
    (actualWindow_pullback_ready s hs).1.2
  rw [port_ActualWindow_address_word_eq,batchPrepareState,signedAddressState_value _ _ _ _ hq]
  have ha := parkedWindow_address 855 (by decide) s
  rw [port_ActualWindow_address_word_eq,port_ActualWindow_address_word_eq] at ha
  have hz : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854=s 870 := by
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [ha,hz]
  rfl


theorem actualBatchedWindowState_selected (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point) (hP : pointStateCoordinates s=fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
        else -windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  rw [actualBatchedWindowState_correct Q hQ hn w s hs P hP,actualWindow_selected_address s hs]

theorem actualBatchedWindowState_valid (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (actualBatchedWindowState Q w s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected Q hQ hn w s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

theorem actualBatchedWindowState_frame (Q : Point) (hQ : order • Q=0) (hn : Q≠0) (w : OddWindow)
    (s : BasisState) (hs : BatchedWindowValid s) (v : Wire) (hv : v∉pointLogicalWires) :
    actualBatchedWindowState Q w s v=s v := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualBatchedWindowState_selected Q hQ hn w s hs P hP]
  simp [pointWrite,hv]

/-- The mixed first-window table may contain infinity; this direct-load theorem
has no nonzero-table-entry hypothesis. -/
theorem actualFirstWindow_coherent (Q : Point) (hQ : order • Q=0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actualFirstWindow.program start).instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (fun s => pointWrite
        (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
          ((2^(16*15)) • G) (tableAddressValue (List.range' 855 16) s)) s))
      (DirectPointLookupValid (List.range' 519 16) 836) := by
  unfold CoherentlyImplementsOn
  rw [actualFirstWindow_run start Q hQ history]
  exact physicalPointLookup_coherent _
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_ActualWindow

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowValidity -/
section Port_WindowValidity

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

theorem batchedWindowValid_address_update (s : BasisState) (hs : BatchedWindowValid s)
    (w : Wire) (hw : w ∈ streamAddress) (b : Bool) : BatchedWindowValid (s[w ↦ b]) := by
  have hw' : 855 ≤ w ∧ w < 871 := by simpa [streamAddress,List.mem_range'_1] using hw
  have hcore (v : Wire) (hv : v < 839) : (s[w ↦ b]) v = s v := by
    simp only [upd]
    rw [if_neg (by dsimp only [Wire] at *; omega)]
  have hx : wireValues (List.range' 263 256) (s[w ↦ b]) = wireValues (List.range' 263 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  have hy : wireValues (List.range' 580 256) (s[w ↦ b]) = wireValues (List.range' 580 256) s := by
    apply List.map_congr_left
    intro v hv
    exact hcore v (by simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  obtain ⟨⟨⟨hclean,hzero,hxbound,hybound⟩,hq⟩,hworkspace⟩ := hs.1
  refine ⟨⟨⟨⟨?_,?_,?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro v hv
    rw [hcore v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)]
    exact hclean v hv
  · rw [hcore 837 (by decide)]; exact hzero
  · rw [hx]; exact hxbound
  · rw [hy]; exact hybound
  · rw [hcore 836 (by decide)]; exact hq
  · intro v hv
    have hv' : 1024 ≤ v := by simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
    have hne : v ≠ w := by dsimp only [Wire] at *; omega
    simpa only [upd,if_neg hne] using hworkspace v hv
  · obtain ⟨P,hP⟩ := hs.2
    refine ⟨P,?_⟩
    simpa only [pointStateCoordinates,hcore 838 (by decide),hx,hy] using hP


private theorem port_WindowValidity_support_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ+φ) := by
  intro s hs
  by_cases h : ψ s=0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h
private theorem port_WindowValidity_support_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])
private theorem port_WindowValidity_support_linear (V : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn V (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn V (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz,hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u=s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,he,map_smul]
    exact port_WindowValidity_support_add (port_WindowValidity_support_smul c (hL s hvs)) (ih hvψ)

theorem batchedWindowValid_fourierClear (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (s : BasisState)
    (hs : BatchedWindowValid s) : BatchedWindowValid (fourierClear ws s) := by
  induction ws generalizing s with
  | nil => exact hs
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (batchedWindowValid_address_update s hs w (hws w (by simp)) false)

theorem batchedWindowValid_fourierBranch (dir : PhaseDir) (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (prior bs : List Bool)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (fourierBranch dir ws prior bs ψ) := by
  apply port_WindowValidity_support_linear _ _ ?_ ψ hψ
  intro s hs
  rw [fourierBranch_ket]
  exact port_WindowValidity_support_smul _ (supportedOn_ket _ _
    (batchedWindowValid_fourierClear ws hws s hs))

theorem batchedWindowValid_H (w : Wire) (hw : w ∈ streamAddress)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (applyGate (.H w) ψ) := by
  apply port_WindowValidity_support_linear _ _ ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact port_WindowValidity_support_add
    (port_WindowValidity_support_smul _ (supportedOn_ket _ _ (batchedWindowValid_address_update s hs w hw false)))
    (port_WindowValidity_support_smul _ (supportedOn_ket _ _ (batchedWindowValid_address_update s hs w hw true)))

theorem batchedWindowValid_prepare (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (ψ : State)
    (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (batchedWindowValid_H w (hws w (by simp)) ψ hψ)


theorem actualBatchedWindowState_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (ψ : State)
    (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w) ψ) := by
  apply port_WindowValidity_support_linear _ _ ?_ ψ hψ
  intro s hs
  simpa [ket] using supportedOn_ket BatchedWindowValid _
    (actualBatchedWindowState_valid Q hQ hn w s hs)

theorem actualBatchedWindow_branch_supported (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (start : Nat) (history : Fin start → Bool)
    (b : InstrumentBranch)
    (hb : b ∈ (((actualBatchedWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn BatchedWindowValid ψ) :
    SupportedOn BatchedWindowValid (b.kraus ψ) := by
  obtain ⟨c,hc⟩ := (actualBatchedWindow_coherent Q hQ hn w start history).branch_coefficient b hb
  rw [hc.on_supported hψ]
  exact port_WindowValidity_support_smul c (actualBatchedWindowState_supported Q hQ hn w ψ hψ)
end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_WindowValidity

/-! Upstream module: ShorECDLP.Submission.Entrant.Streaming.Challenge.FirstValidity -/
section Port_FirstValidity

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1

private theorem port_FirstValidity_zero_word (n : Nat) : boolWordToNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,ih]
private theorem port_FirstValidity_zero_read (ws : List Wire) (s : BasisState)
    (hs : ∀ w ∈ ws, s w = false) :
    wireValues ws s = List.replicate ws.length false := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wireValues,List.map_cons,List.length_cons,List.replicate_succ]
    rw [hs w (by simp)]
    exact congrArg (false :: ·) (ih (fun v hv => hs v (List.mem_cons_of_mem w hv)))

/-- Before direct loading, only the query flag and address register may be nonzero. -/
def FirstWindowInput (s : BasisState) : Prop :=
  s 836 = true ∧ ∀ v, v ≠ 836 → v ∉ streamAddress → s v = false

theorem firstWindowInput_start : FirstWindowInput (zeroBasisState[836 ↦ true]) := by
  constructor
  · simp [upd]
  · intro v hv _
    simp [upd,hv,zeroBasisState]

theorem firstWindowInput_update (s : BasisState) (hs : FirstWindowInput s)
    (w : Wire) (hw : w ∈ streamAddress) (b : Bool) : FirstWindowInput (s[w ↦ b]) := by
  have hw' : 855 ≤ w ∧ w < 871 := by simpa [streamAddress,List.mem_range'_1] using hw
  have hwb : 855 ≤ w := hw'.1
  constructor
  · simpa only [upd,if_neg (by dsimp only [Wire] at *; omega : (836:Wire) ≠ w)] using hs.1
  · intro v hv ha
    have hvw : v ≠ w := by intro he; subst v; exact ha hw
    simpa only [upd,if_neg hvw] using hs.2 v hv ha

theorem firstWindowInput_ready (s : BasisState) (hs : FirstWindowInput s) :
    BatchedPointReady s := by
  have hz (v : Wire) (hv : v < 836) : s v = false :=
    hs.2 v (by dsimp only [Wire] at *; omega) (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)
  have hx : wireValues (List.range' 263 256) s = List.replicate 256 false := by
    exact (port_FirstValidity_zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  have hy : wireValues (List.range' 580 256) s = List.replicate 256 false := by
    exact (port_FirstValidity_zero_read _ s (fun v hv => hz v (by
      simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega))).trans
      (by simp only [List.length_range'])
  refine ⟨⟨⟨?_,?_,?_,?_⟩,hs.1⟩,?_⟩
  · intro v hv
    exact hz v (by simp only [List.mem_append,List.mem_range'_1] at hv; dsimp only [Wire] at *; omega)
  · exact hs.2 837 (by decide) (by simp [streamAddress])
  · rw [hx]; rw [port_FirstValidity_zero_word]; norm_num [ShorECDLP.p]
  · rw [hy]; rw [port_FirstValidity_zero_word]; norm_num [ShorECDLP.p]
  · intro v hv
    have hb : 1024 ≤ v := by
      simp only [batchWorkspace,List.mem_append,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact hs.2 v (by dsimp only [Wire] at *; omega) (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)

theorem firstWindowInput_lookup (s : BasisState) (hs : FirstWindowInput s) :
    DirectPointLookupValid (List.range' 519 16) 836 s := by
  refine ⟨?_,?_,hs.1⟩
  · intro v hv
    apply hs.2
    · simp only [List.mem_range'_1] at hv; dsimp only [Wire] at *; omega
    · simp only [List.mem_range'_1] at hv
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega
  · intro v hv
    have hb : v < 839 := by
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    have hn : v ≠ 836 := by
      simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hv
      dsimp only [Wire] at *; omega
    exact hs.2 v hn (by
      simp only [streamAddress,List.mem_range'_1]; try dsimp only [Wire] at *
      omega)

theorem firstWindowInput_pointWrite (s : BasisState) (hs : FirstWindowInput s) (P : Point) :
    BatchedWindowValid (pointWrite P s) :=
  ⟨pointWrite_batchedReady P s (firstWindowInput_ready s hs),P,pointWrite_coordinates P s⟩



private theorem port_FirstValidity_support_add {V : BasisState → Prop} {ψ φ : State}
    (hψ : SupportedOn V ψ) (hφ : SupportedOn V φ) : SupportedOn V (ψ+φ) := by
  intro s hs
  by_cases h : ψ s=0
  · exact hφ s (by simpa [h] using hs)
  · exact hψ s h
private theorem port_FirstValidity_support_smul {V : BasisState → Prop} {ψ : State} (c : ℂ)
    (hψ : SupportedOn V ψ) : SupportedOn V (c • ψ) := by
  intro s hs
  apply hψ s
  intro h
  exact hs (by simp [h])
private theorem port_FirstValidity_support_linear (V W : BasisState → Prop) (L : State →ₗ[ℂ] State)
    (hL : ∀ s, V s → SupportedOn W (L (ket s))) (ψ : State)
    (hψ : SupportedOn V ψ) : SupportedOn W (L ψ) := by
  classical
  induction ψ using Finsupp.induction with
  | zero => simp
  | single_add s c ψ hs hc ih =>
    have hz : ψ s=0 := by simpa using hs
    have hvs : V s := hψ s (by simp [hz,hc])
    have hvψ : SupportedOn V ψ := by
      intro u hu
      apply hψ u
      by_cases he : u=s
      · subst u; exact (hu hz).elim
      · simpa [he] using hu
    have he : Finsupp.single s c=c • ket s := by ext u; simp [ket]
    rw [map_add,he,map_smul]
    exact port_FirstValidity_support_add (port_FirstValidity_support_smul c (hL s hvs)) (ih hvψ)

theorem firstWindowInput_H (w : Wire) (hw : w ∈ streamAddress)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn FirstWindowInput (applyGate (.H w) ψ) := by
  apply port_FirstValidity_support_linear FirstWindowInput FirstWindowInput (applyGate (.H w)) ?_ ψ hψ
  intro s hs
  rw [applyGate_ket]
  exact port_FirstValidity_support_add
    (port_FirstValidity_support_smul _ (supportedOn_ket _ _ (firstWindowInput_update s hs w hw false)))
    (port_FirstValidity_support_smul _ (supportedOn_ket _ _ (firstWindowInput_update s hs w hw true)))

theorem firstWindowInput_prepare (ws : List Wire)
    (hws : ∀ w ∈ ws, w ∈ streamAddress) (ψ : State)
    (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn FirstWindowInput (Quantum.run (ws.map Gate.H) ψ) := by
  induction ws generalizing ψ with
  | nil => exact hψ
  | cons w ws ih =>
    exact ih (fun v hv => hws v (List.mem_cons_of_mem w hv)) _
      (firstWindowInput_H w (hws w (by simp)) ψ hψ)

noncomputable def actualFirstWindowState (Q : Point) (s : BasisState) : BasisState :=
  pointWrite (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
    ((2^(16*15)) • G) (tableAddressValue (List.range' 855 16) s)) s

theorem actualFirstWindowState_supported (Q : Point) (ψ : State)
    (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn BatchedWindowValid
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q) ψ) := by
  apply port_FirstValidity_support_linear FirstWindowInput BatchedWindowValid _ ?_ ψ hψ
  intro s hs
  rw [show Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q) (ket s) =
      ket (actualFirstWindowState Q s) from by simp only [ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]]
  exact supportedOn_ket _ _ (firstWindowInput_pointWrite s hs _)

theorem actualFirstWindow_coherent_input (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actualFirstWindow.program start).instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualFirstWindowState Q)) FirstWindowInput := by
  obtain ⟨cs,ha,hm⟩ := actualFirstWindow_coherent Q hQ start history
  exact ⟨cs,ha.imp (fun _ _ hb s hs => hb s (firstWindowInput_lookup s hs)),hm⟩

theorem actualFirstWindow_branch_supported (Q : Point) (hQ : order • Q = 0)
    (start : Nat) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((actualFirstWindow.program start).instantiate
      (readConstant coefficientAt Q) history).run)
    (ψ : State) (hψ : SupportedOn FirstWindowInput ψ) :
    SupportedOn BatchedWindowValid (b.kraus ψ) := by
  obtain ⟨c,hc⟩ := (actualFirstWindow_coherent_input Q hQ start history).branch_coefficient b hb
  rw [hc.on_supported hψ]
  exact port_FirstValidity_support_smul c (actualFirstWindowState_supported Q ψ hψ)

end ShorECDLP.Paper2607_13816.ChallengeMigration

end Port_FirstValidity
