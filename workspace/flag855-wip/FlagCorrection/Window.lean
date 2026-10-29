import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Correctness
import ShorECDLP.Submission.Entrant.Streaming.Challenge.BatchedWindowCoherent

namespace ShorECDLP.FlagCorrection

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
attribute [local irreducible] flagCorrectionState ShorECDLP.Paper2607_13816.pointWrite

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs, hc, hm⟩ := h
  exact ⟨cs, hc.imp (fun _ _ hb s hs => hb s (hp s hs)), hm⟩

def flagPlacedProgram (w : OddWindow) : FixedSegment 983040 :=
  flagCorrectionProgram (batchWindowRows w)

noncomputable def flagPlacedSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  flagCorrectionSource (readConstant coefficientAt Q) (batchWindowRows w)

noncomputable def flagPlacedState (Q : Point) (w : OddWindow) : BasisState → BasisState :=
  flagCorrectionState (readConstant coefficientAt Q) (batchWindowRows w)

theorem flagPlacedProgram_run (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (flagPlacedProgram w start) (readConstant coefficientAt Q) history =
      (flagPlacedSource Q w).run :=
  flagCorrectionProgram_run _ _ _ _

theorem batchWindowTree_route_direct (s : BasisState) :
    batchWindowTree.routeLabel s = tableAddressValue pointLookupAddress s := by
  rw [batchWindowTree, tableAddressTree_route, zero_add, one_mul]

theorem flagPlacedSource_coherent (Q : Point) (w : OddWindow) :
    CoherentlyImplementsOn (flagPlacedSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (flagPlacedState Q w)) FlagReady :=
  flagCorrectionSource_coherent _ _

noncomputable def flagSignedState (Q : Point) (w : OddWindow) (s : BasisState) : BasisState :=
  windowYNegateState (flagPlacedState Q w (windowYNegateState s))

noncomputable def flagSignedSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (windowYNegate.seq (flagPlacedSource Q w)).seq windowYNegate

theorem signedReady_middle_data (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : SignedBatchReady Q w s) :
    let t := windowYNegateState s
    ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y) (P' : Point),
      PointLookupValid t ∧
      constantPoint Q (coefficientAt
        (batchWindowRows w (batchWindowTree.routeLabel t))) = .some hC ∧
      order • (.some hC : Point) = 0 ∧ (.some hC : Point) ≠ 0 ∧
      pointStateCoordinates t = fig14EncodedEquiv x y (fig14PointEncoding P') := by
  dsimp only
  obtain ⟨hr, x, y, hC, hrow, P, hdata⟩ := hs
  let t := windowYNegateState s
  let P' : Point := if s 854 then P else -P
  have ht : BatchedPointReady t := windowYNegateState_batchedReady s hr
  have hroute : batchWindowTree.routeLabel t =
      batchWindowTree.routeLabel (relabelBasis batchPlacement.symm t) := by
    rw [batchWindowTree_route_direct, batchWindowTree_route]
  have hrow' : constantPoint Q
      (coefficientAt (batchWindowRows w (batchWindowTree.routeLabel t))) = .some hC := by
    rw [hroute]
    exact hrow
  have hpoint : windowPoint Q w (tableAddressValue pointLookupAddress t) = .some hC := by
    rw [← batchWindowTree_route t, ← hroute]
    unfold batchWindowRows at hrow'
    rw [coefficientAt_window, oddWindowCoefficients_point w _ Q hQ] at hrow'
    have hb : batchWindowTree.routeLabel t < 32768 := by
      rw [batchWindowTree_route_direct]
      exact tableAddressValue_lt pointLookupAddress t
    simpa only [Nat.mod_eq_of_lt hb] using hrow'
  have horder : order • (.some hC : Point) = 0 := by
    rw [← hpoint]
    exact windowPoint_order Q hQ w _
  have hC0 : (.some hC : Point) ≠ 0 := by
    rw [← hpoint]
    exact windowPoint_ne_zero Q hQ hn w _
  have hd : pointStateCoordinates t = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hr.1.1, hdata]
    cases hsg : s 854
    · simpa only [hsg, Bool.false_eq_true, ite_false, P', fig14PointEncoding_neg,
        encodedNegY] using fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg, ite_true, P']
  exact ⟨x, y, hC, P', ht.1, hrow', horder, hC0, hd⟩

theorem flagPlaced_middle_pointWrite (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : SignedBatchReady Q w s) :
    let t := windowYNegateState s
    ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y) (P' : Point),
      flagPlacedState Q w t = pointWrite (P' + .some hC) t ∧
      Secp256k1ZeroAllowedInputValid (flagPlacedState Q w t) ∧
      pointStateCoordinates (flagPlacedState Q w t) = fig14PointEncoding (P' + .some hC) := by
  dsimp only
  obtain ⟨x, y, hC, P', ht, hrow, horder, hC0, hd⟩ :=
    signedReady_middle_data Q hQ hn w s hs
  have hc := flagCorrectionState_pointWrite_all coefficientAt Q (batchWindowRows w)
    (windowYNegateState s) ht hC hrow horder hC0 P' hd
  dsimp only [flagPlacedState] at hc ⊢
  refine ⟨x, y, hC, P', hc.1, ?_, ?_⟩
  · rw [hc.1]
    exact pointWrite_valid _ _ ht.1
  · rw [hc.1, pointWrite_coordinates]

theorem flagSignedState_pointWrite_explicit (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hr : BatchedPointReady s)
    (x y : Fp) (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm
        (windowYNegateState s))))) = .some hC)
    (P : Point) (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    flagSignedState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress s)
        else -windowPoint Q w (tableAddressValue pointLookupAddress s)) s := by
  let t := windowYNegateState s
  let P' : Point := if s 854 then P else -P
  have ht : BatchedPointReady t := windowYNegateState_batchedReady s hr
  have hroute : batchWindowTree.routeLabel t =
      batchWindowTree.routeLabel (relabelBasis batchPlacement.symm t) := by
    rw [batchWindowTree_route_direct, batchWindowTree_route]
  have hrow' : constantPoint Q
      (coefficientAt (batchWindowRows w (batchWindowTree.routeLabel t))) = .some hC := by
    rw [hroute]
    exact hrow
  have hpoint : windowPoint Q w (tableAddressValue pointLookupAddress t) = .some hC := by
    rw [← batchWindowTree_route t, ← hroute]
    unfold batchWindowRows at hrow'
    rw [coefficientAt_window, oddWindowCoefficients_point w _ Q hQ] at hrow'
    have hb : batchWindowTree.routeLabel t < 32768 := by
      rw [batchWindowTree_route_direct]
      exact tableAddressValue_lt pointLookupAddress t
    simpa only [Nat.mod_eq_of_lt hb] using hrow'
  have horder : order • (.some hC : Point) = 0 := by
    rw [← hpoint]
    exact windowPoint_order Q hQ w _
  have hC0 : (.some hC : Point) ≠ 0 := by
    rw [← hpoint]
    exact windowPoint_ne_zero Q hQ hn w _
  have hd : pointStateCoordinates t = fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hr.1.1, hdata]
    cases hsg : s 854
    · simpa only [hsg, Bool.false_eq_true, ite_false, P', fig14PointEncoding_neg,
        encodedNegY] using fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg, ite_true, P']
  have hc := flagCorrectionState_pointWrite_all coefficientAt Q (batchWindowRows w) t ht.1
    hC hrow' horder hC0 P' hd
  dsimp only [flagPlacedState] at hc
  let u := flagPlacedState Q w t
  have huEq : u = pointWrite (P' + .some hC) t := by
    dsimp only [u, flagPlacedState]
    exact hc.1
  have huValid : Secp256k1ZeroAllowedInputValid u := by
    rw [huEq]
    exact pointWrite_valid _ _ ht.1.1
  have huCoord : pointStateCoordinates u = fig14PointEncoding (P' + .some hC) := by
    rw [huEq, pointWrite_coordinates]
  have hsign : u 854 = s 854 := by
    rw [huEq, pointWrite_frame]
    · exact (windowYNegateState_correct s hr.1.1).2 854 (by decide)
    · decide +kernel
  have hlast := windowYNegateState_pointWrite (P' + .some hC) u huValid huCoord
  have hpointFinal : (if s 854 then P' + .some hC else -(P' + .some hC)) =
      P + if s 854 then (.some hC : Point) else -(.some hC) := by
    cases hsg : s 854 <;> simp [P', hsg, add_comm]
  have haddr := windowYNegateState_address s hr.1.1
  have hCeq : windowPoint Q w (tableAddressValue pointLookupAddress s) = .some hC := by
    rw [← haddr]
    exact hpoint
  rw [hCeq]
  unfold flagSignedState
  rw [hlast, hsign, hpointFinal, huEq, pointWrite_overwrite]
  apply pointWrite_frame_eq
  intro v hv
  apply (windowYNegateState_correct s hr.1.1).2 v
  intro hy
  exact hv (List.mem_append_right _ (List.mem_append_left _ hy))

theorem flagSignedState_pointWrite (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) (s : BasisState) (hs : SignedBatchReady Q w s) :
    ∃ P : Point, flagSignedState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress s)
        else -windowPoint Q w (tableAddressValue pointLookupAddress s)) s := by
  obtain ⟨hr, x, y, hC, hrow, P, hdata⟩ := hs
  exact ⟨P, flagSignedState_pointWrite_explicit Q hQ hn w s hr x y hC hrow P hdata⟩

theorem flagSignedSource_coherent (Q : Point) (hQ : order • Q = 0) (hn : Q ≠ 0)
    (w : OddWindow) :
    CoherentlyImplementsOn (flagSignedSource Q w)
      (Finsupp.lmapDomain ℂ ℂ (flagSignedState Q w)) (SignedBatchReady Q w) := by
  have hneg : CoherentlyImplementsOn windowYNegate
      (Finsupp.lmapDomain ℂ ℂ windowYNegateState) (SignedBatchReady Q w) :=
    restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (flagPlacedSource_coherent Q w) (by
    intro s hs
    exact (pointLookupValid_flagDomain _
      (windowYNegateState_batchedReady s hs.1).1).1)
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨x, y, hC, P', heq, hv, hc⟩ := flagPlaced_middle_pointWrite Q hQ hn w s hs
    exact hv)
  simpa only [flagSignedSource, flagSignedState, adaptive_seq_assoc] using hlast

def flagBatchedWindowSegments (w : OddWindow) : List (FixedSegment 983040) :=
  [sharedCoordinateProgram w, sharedYNegateProgram w, flagPlacedProgram w,
    sharedYNegateProgram w]

noncomputable def flagBatchedWindowSources (Q : Point) (w : OddWindow) :
    List AdaptiveCircuit :=
  [signedLookupCoordinateProgram (fun l => fieldValue (windowPoint Q w l) .x)
    (fun l => fieldValue (windowPoint Q w l) .y), windowYNegate,
    flagPlacedSource Q w, windowYNegate]

def flagBatchedWindowCore (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start + count) :=
  sequenceProgram 983040 (flagBatchedWindowSegments w) start

theorem flagBatchedWindowCore_run (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledRun (flagBatchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (flagBatchedWindowSources Q w)).run := by
  apply sequenceProgram_run
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h
    exact sharedCoordinateProgram_run w cursor Q hQ h
  · intro cursor h
    exact sharedYNegateProgram_run w cursor _ h
  · intro cursor h
    exact flagPlacedProgram_run w cursor Q h
  · intro cursor h
    exact sharedYNegateProgram_run w cursor _ h

noncomputable def flagBatchedWindowState (Q : Point) (w : OddWindow)
    (s : BasisState) : BasisState :=
  flagSignedState Q w (signedLookupCoordinateState
    (fun a => fieldValue (windowPoint Q w a) .x)
    (fun a => fieldValue (windowPoint Q w a) .y) s)

theorem flagBatchedWindowSources_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) :
    CoherentlyImplementsOn (sequenceCircuit (flagBatchedWindowSources Q w))
      (Finsupp.lmapDomain ℂ ℂ (flagBatchedWindowState Q w)) BatchedWindowValid := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  have hfirst : CoherentlyImplementsOn (signedLookupCoordinateProgram xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (signedLookupCoordinateProgram_coherent xs ys) (fun s hs => hs.1.1)
  have h := composeCoherent hfirst (flagSignedSource_coherent Q hQ hn w) (by
    intro s hs
    obtain ⟨hs, P, hP⟩ := hs
    cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
    | some hC => exact batchedWindow_coordinate_ready Q hQ w s hs hC he P hP)
  simpa only [flagBatchedWindowSources, sequenceCircuit, flagSignedSource,
    adaptive_seq_assoc, adaptive_seq_done, flagBatchedWindowState, xs, ys] using h

theorem flagBatchedWindowCore_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn
      ((flagBatchedWindowCore w start).2.instantiate (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (flagBatchedWindowState Q w)) BatchedWindowValid := by
  have h := flagBatchedWindowSources_coherent Q hQ hn w
  unfold CoherentlyImplementsOn at h ⊢
  have hr := flagBatchedWindowCore_run w start Q hQ history
  unfold compiledRun at hr
  rw [hr]
  exact h

theorem flagBatchedWindowState_finite (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : windowPoint Q w (tableAddressValue pointLookupAddress s) = .some hC)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    flagBatchedWindowState Q w s =
      pointWrite (P + if s 854 then (.some hC : Point) else -(.some hC)) s := by
  let xs := fun a => fieldValue (windowPoint Q w a) .x
  let ys := fun a => fieldValue (windowPoint Q w a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have ha : tableAddressValue pointLookupAddress t = tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress, List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress, List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854 = s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hr' : constantPoint Q (coefficientAt (batchWindowRows w
      (batchWindowTree.routeLabel (relabelBasis batchPlacement.symm
        (windowYNegateState t))))) = .some hC := by
    rw [batchWindowTree_route, windowYNegateState_address t ht.1.1, ha]
    unfold batchWindowRows
    rw [coefficientAt_window, oddWindowCoefficients_point w _ Q hQ]
    have hb : tableAddressValue pointLookupAddress s < 32768 :=
      tableAddressValue_lt pointLookupAddress s
    simpa only [Nat.mod_eq_of_lt hb] using hr
  have hx : xs (tableAddressValue pointLookupAddress s) = x.val := by
    simp [xs, hr, fieldValue, pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s) = y.val := by
    simp [ys, hr, fieldValue, pointCoordinates]
  have hyv : signedPointTableValue ys s = (if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases s 854 <;> simp [ZMod.neg_val']
  have hd : pointStateCoordinates t =
      fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1, hx, hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2, hP]
  have he := flagSignedState_pointWrite_explicit Q hQ hn w t ht x y hC hr' P hd
  change flagSignedState Q w t = _
  rw [he, hz, ha, hr]
  apply pointWrite_frame_eq
  intro v hv
  exact signedLookupCoordinateState_frame xs ys s hs.1 v
    (fun hx => hv (List.mem_append_left _ hx))
    (fun hy => hv (List.mem_append_right _ (List.mem_append_left _ hy)))

theorem flagBatchedWindowState_correct (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    flagBatchedWindowState Q w s = pointWrite
      (P + if s 854 then windowPoint Q w (tableAddressValue pointLookupAddress s)
        else -windowPoint Q w (tableAddressValue pointLookupAddress s)) s := by
  cases he : windowPoint Q w (tableAddressValue pointLookupAddress s) with
  | zero => exact False.elim (windowPoint_ne_zero Q hQ hn w _ he)
  | some hC => exact flagBatchedWindowState_finite Q hQ hn w s hs hC he P hP

end ShorECDLP.FlagCorrection
