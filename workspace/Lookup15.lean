import ShorECDLP.Submission.Entrant.Main

namespace ShorECDLP.Entrant.Lookup15Scratch

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

def address : List Wire := List.range' 839 14
def path : List Wire := List.range' 519 14
def tree : UnaryActionTree := tableAddressTree address 0 1

theorem tree_layout (c : Option (Fin 4)) : tree.Layout (ipxControl c) path := by
  apply tableAddressTree_layout _ _ _ _ _ (by decide)
  cases c with
  | none => decide +kernel
  | some k => fin_cases k <;> decide +kernel

theorem tree_outside (c : Option (Fin 4)) (w : Wire)
    (hw : w ∈ ipxControl c :: tree.indexWires.dedup ++ path) :
    w ∉ pointLogicalWires := by
  intro hp
  have hi : w ∈ address ∨ w = ipxControl c ∨ w ∈ path := by
    have ht : w ∈ tree.indexWires ↔ w ∈ address := by
      exact tableAddressTree_mem_index address 0 1 w
    simp only [List.mem_cons,List.mem_append,List.mem_dedup,ht] at hw
    aesop
  have hc := ipxControl_lt c
  have hb := pointLogicalWires_bounds w hp
  simp only [address,path,List.mem_range'_1] at hi
  dsimp only [Wire] at *
  omega

theorem geometry : IpxGeometry tree path := by
  refine ⟨tree_layout,tree_outside,?_,?_⟩
  · intro w hw k he
    have h := (tableAddressTree_mem_index address 0 1 w).mp hw
    have hk := ipxFlag_lt k
    simp only [address,List.mem_range'_1] at h
    dsimp only [Wire] at *
    omega
  · intro w hw k he
    have hk := ipxFlag_lt k
    simp only [path,List.mem_range'_1] at hw
    dsimp only [Wire] at *
    omega

theorem tree_nodes : tree.internalNodes = 16383 := by
  have h := tableAddressTree_nodes address 0 1
  change tree.internalNodes + 1 = 16384 at h
  omega

theorem route (s : BasisState) : tree.routeLabel s = tableAddressValue address s := by
  rw [tree,tableAddressTree_route,zero_add,one_mul]

theorem address_mod (s : BasisState) :
    tableAddressValue address s = tableAddressValue pointLookupAddress s % 16384 := by
  have he : pointLookupAddress = address ++ [853] := by decide
  have hb := tableAddressValue_lt address s
  have hp : 2^address.length = 16384 := by norm_num [address]
  rw [hp] at hb
  rw [he, Single.address_append]
  rw [hp]
  simp only [tableAddressValue]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

def rows (label : Nat) : Fin 32768 := ⟨label % 32768, Nat.mod_lt _ (by decide)⟩

noncomputable def source (coeffs : Fin 32768 → PointCoeff) (Q : Point) : AdaptiveCircuit :=
  ipxSourceOps (readConstant coeffs Q) rows tree path ipxSchedule

noncomputable def state (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (st : BasisState) : BasisState :=
  Classical.run (ipxUnitaryOps (readConstant coeffs Q) rows tree path ipxSchedule) st

attribute [local irreducible] ipxUnitaryOps ipxSourceOps

theorem source_state (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (source coeffs Q) (Finsupp.lmapDomain ℂ ℂ (state coeffs Q))
      (IpxInv path) := by
  have h := ipxSourceOps_coherent coeffs Q rows tree path geometry ipxSchedule
  apply h.congrIdeal
  intro st _
  rw [run_ket_agrees_classical _ st (ipxUnitaryOps_HPFree _ _ _ _ _)]
  simp only [state,ket,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]

theorem inv_of_valid (s : BasisState) (hv : Secp256k1ZeroAllowedInputValid s)
    (hq : s 836 = true) : IpxInv path s := by
  refine ⟨?_,?_,?_,hq⟩
  · intro w hw
    apply hv.1 w
    simp only [path,List.mem_range'_1] at hw
    simp only [List.mem_append,List.mem_range'_1]
    omega
  · intro w hw
    apply hv.1 w
    simp only [ipxScratch,List.mem_range'_1] at hw
    simp only [List.mem_append,List.mem_range'_1]
    omega
  · exact hv.1 4 (by simp)

theorem state_frame (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState)
    (hs : IpxInv path s) (w : Wire) (hw : w ∉ pointLogicalWires)
    (hf : ∀ k, w ≠ ipxFlag k) : state coeffs Q s w = s w :=
  (ipxUnitary_model coeffs Q rows tree path geometry ipxSchedule s hs).2.2 w hw hf

theorem state_pointWrite (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (st : BasisState) (hv : Secp256k1ZeroAllowedInputValid st) (hq : st 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (rows (tree.routeLabel st))) = .some hC)
    (hord : order • (.some hC : Point) = 0) (P : Point)
    (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P)) :
    state coeffs Q st = pointWrite (P + .some hC) st := by
  have hinv := inv_of_valid st hv hq
  have hm := ipxUnitary_model coeffs Q rows tree path geometry ipxSchedule st hinv
  have hA : st ∘ accumulatorPort = coordinateWordBits
      (fig14EncodedEquiv x y (fig14PointEncoding P)) :=
    (accumulatorPort_coordinates st hv).trans (congrArg coordinateWordBits hdata)
  have hF : (fun k => st (ipxFlag k)) = fun _ => false := funext (ipxFlags_clean st hv)
  have hres := hm.1
  rw [hA,hF] at hres
  change _ = ipxModel _ _ at hres
  rw [ipxModel_point coeffs Q _ hC hr hord P] at hres
  have hacc := congrArg Prod.fst hres
  have hfl := congrArg Prod.snd hres
  dsimp only at hacc hfl
  apply accumulator_word_frame_ext
  · exact (accumulatorPort_encoding_iff _ _).mp hacc
  · intro v hv'
    by_cases hk : ∃ k, v = ipxFlag k
    · obtain ⟨k,rfl⟩ := hk
      exact (congrFun hfl k).trans (ipxFlags_clean st hv k).symm
    · push_neg at hk
      exact hm.2.2 v hv' hk

noncomputable def signedState (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) : BasisState :=
  windowYNegateState (state coeffs Q (windowYNegateState s))

theorem pointWrite_frame_eq (P : Point) (s t : BasisState)
    (h : ∀ w, w ∉ pointLogicalWires → s w = t w) : pointWrite P s = pointWrite P t := by
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · simp only [pointWrite,if_pos hw]
  · simp only [pointWrite,if_neg hw,h w hw]

theorem signedState_pointWrite (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (rows (tree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0) (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    signedState coeffs Q s =
      pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have htq : windowYNegateState s 836 = true :=
    ((windowYNegateState_correct s hs).2 836 (by decide)).trans hq
  have hd : pointStateCoordinates (windowYNegateState s) =
      fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  have he := state_pointWrite coeffs Q _ ht htq hC hr hord P' hd
  have hsign : state coeffs Q (windowYNegateState s) 854 = s 854 :=
    (state_frame coeffs Q _ (inv_of_valid _ ht htq) 854 (by decide +kernel)
      (ipxFlag_ne_of_ge 854 (by decide))).trans
      ((windowYNegateState_correct s hs).2 854 (by decide +kernel))
  have hv : Secp256k1ZeroAllowedInputValid (state coeffs Q (windowYNegateState s)) := by
    rw [he]
    exact pointWrite_valid _ _ ht
  have hc : pointStateCoordinates (state coeffs Q (windowYNegateState s)) =
      fig14PointEncoding (P' + .some hC) := by
    rw [he]
    exact pointWrite_coordinates _ _
  unfold signedState
  rw [windowYNegateState_pointWrite (P' + .some hC) _ hv hc,hsign,he,pointWrite_overwrite]
  have hpoint : (if s 854 then P' + .some hC else -(P' + .some hC)) =
      P + if s 854 then .some hC else -(.some hC) := by
    cases hsg : s 854 <;> simp [P',hsg,add_comm]
  rw [hpoint]
  apply pointWrite_frame_eq
  intro v hv'
  apply (windowYNegateState_correct s hs).2 v
  intro hy
  exact hv' (List.mem_append_right _ (List.mem_append_left _ hy))

noncomputable def batchedState (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) : BasisState :=
  signedState coeffs Q (signedLookupCoordinateState
    (fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .x)
    (fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .y) s)

def Aliased (coeffs : Fin 32768 → PointCoeff) : Prop :=
  ∀ a, coeffs a = coeffs ⟨a.val % 16384,
    by have h := Nat.mod_lt a.val (by decide : 0 < 16384); omega⟩

theorem rows_route (s : BasisState) :
    rows (tree.routeLabel s) =
      ⟨tableAddressValue pointLookupAddress s % 16384,
        by omega⟩ := by
  apply Fin.ext
  rw [route,address_mod]
  simp only [rows]
  have hb := tableAddressValue_lt pointLookupAddress s
  simp only [pointLookupAddress,List.length_range'] at hb
  omega

theorem tablePoint_aliased (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (a : Nat) :
    Single.Physical.tablePoint coeffs Q (a % 16384) = Single.Physical.tablePoint coeffs Q a := by
  unfold Single.Physical.tablePoint
  rw [ha ⟨a % 32768, Nat.mod_lt _ (by decide)⟩]
  congr 2
  apply Fin.ext
  simp only
  omega

theorem constantPoint_aliased (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (a : Nat) :
    constantPoint Q (coeffs ⟨a % 16384, by omega⟩) =
      Single.Physical.tablePoint coeffs Q a := by
  unfold Single.Physical.tablePoint
  rw [ha ⟨a % 32768, Nat.mod_lt _ (by decide)⟩]
  congr 2
  apply Fin.ext
  simp only
  omega

theorem batchedState_finite (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0) (s : BasisState)
    (hs : BatchedPointReady s) {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : Single.Physical.tablePoint coeffs Q (tableAddressValue pointLookupAddress s) = .some hC)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    batchedState coeffs Q s =
      pointWrite (P + if s 854 then .some hC else -(.some hC)) s := by
  let xs := fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have haddr : tableAddressValue pointLookupAddress t = tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854 = s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hrow : constantPoint Q (coeffs (rows (tree.routeLabel (windowYNegateState t)))) =
      .some hC := by
    rw [rows_route]
    have hm : tableAddressValue pointLookupAddress (windowYNegateState t) % 16384 =
        tableAddressValue pointLookupAddress s % 16384 := by
      rw [windowYNegateState_address t ht.1.1,haddr]
    have hf : (⟨tableAddressValue pointLookupAddress (windowYNegateState t) % 16384,
        by omega⟩ : Fin 32768) = ⟨tableAddressValue pointLookupAddress s % 16384, by omega⟩ :=
      Fin.ext hm
    rw [hf]
    exact (constantPoint_aliased coeffs Q ha _).trans hr
  have hx : xs (tableAddressValue pointLookupAddress s) = x.val := by
    simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s) = y.val := by
    simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s = (if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases h : s 854
    · simp only [Bool.false_eq_true,if_false]
      exact (ZMod.neg_val' y).symm
    · simp only [if_true]
  have hd : pointStateCoordinates t =
      fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  have he := signedState_pointWrite coeffs Q t ht.1.1 ht.1.2 hC hrow
    (hr ▸ Single.Physical.tablePoint_order coeffs Q hQ _) P hd
  change signedState coeffs Q t = _
  rw [he,hz]
  apply pointWrite_frame_eq
  intro v hv
  exact signedLookupCoordinateState_frame xs ys s hs.1 v
    (fun hx => hv (List.mem_append_left _ hx))
    (fun hy => hv (List.mem_append_right _ (List.mem_append_left _ hy)))

theorem batchedState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0) (s : BasisState)
    (hs : BatchedPointReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    batchedState coeffs Q s = pointWrite
      (P + if s 854 then Single.Physical.tablePoint coeffs Q (tableAddressValue pointLookupAddress s)
        else -Single.Physical.tablePoint coeffs Q (tableAddressValue pointLookupAddress s)) s := by
  cases he : Single.Physical.tablePoint coeffs Q (tableAddressValue pointLookupAddress s) with
  | zero => exact False.elim (hn _ he)
  | some hC => exact batchedState_finite coeffs Q ha hQ s hs hC he P hP

def Ready (coeffs : Fin 32768 → PointCoeff) (Q : Point) (s : BasisState) : Prop :=
  BatchedPointReady s ∧ ∃ (x y : Fp) (hC : curve.toAffine.Nonsingular x y),
    constantPoint Q (coeffs (rows (tree.routeLabel (windowYNegateState s)))) = .some hC ∧
    order • (.some hC : Point) = 0 ∧ ∃ P : Point, pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)

theorem signedState_middle_ready (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836 = true)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : constantPoint Q (coeffs (rows (tree.routeLabel (windowYNegateState s)))) = .some hC)
    (hord : order • (.some hC : Point) = 0) (P : Point)
    (hdata : pointStateCoordinates s =
      fig14EncodedEquiv x (if s 854 then y else -y) (fig14PointEncoding P)) :
    Secp256k1ZeroAllowedInputValid (state coeffs Q (windowYNegateState s)) := by
  let P' : Point := if s 854 then P else -P
  have ht := windowYNegateState_ready s hs
  have htq : windowYNegateState s 836 = true :=
    ((windowYNegateState_correct s hs).2 836 (by decide)).trans hq
  have hd : pointStateCoordinates (windowYNegateState s) =
      fig14EncodedEquiv x y (fig14PointEncoding P') := by
    rw [windowYNegateState_coordinates s hs,hdata]
    cases hsg : s 854
    · simpa only [hsg,Bool.false_eq_true,ite_false,P',fig14PointEncoding_neg,encodedNegY] using
        fig14EncodedEquiv_negY x y (fig14PointEncoding P)
    · simp only [hsg,ite_true,P']
  rw [state_pointWrite coeffs Q _ ht htq hC hr hord P' hd]
  exact pointWrite_valid _ _ ht

noncomputable def signedSource (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    AdaptiveCircuit := (windowYNegate.seq (source coeffs Q)).seq windowYNegate

private theorem restrictCoherent {a : AdaptiveCircuit} {v : State →ₗ[ℂ] State}
    {P R : BasisState → Prop} (h : CoherentlyImplementsOn a v R)
    (hp : ∀ s, P s → R s) : CoherentlyImplementsOn a v P := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s (hp s hs)),hm⟩

theorem signedSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    CoherentlyImplementsOn (signedSource coeffs Q)
      (Finsupp.lmapDomain ℂ ℂ (signedState coeffs Q)) (Ready coeffs Q) := by
  have hneg : CoherentlyImplementsOn windowYNegate
      (Finsupp.lmapDomain ℂ ℂ windowYNegateState) (Ready coeffs Q) :=
    restrictCoherent windowYNegate_coherent (fun s hs => hs.1.1.1)
  have hfirst := composeCoherent hneg (source_state coeffs Q) (fun s hs => by
    have hn := windowYNegateState_batchedReady s hs.1
    exact inv_of_valid _ hn.1.1 hn.1.2)
  have hlast := composeCoherent hfirst windowYNegate_coherent (by
    intro s hs
    obtain ⟨hr,x,y,hC,hrow,hord,P,hdata⟩ := hs
    exact signedState_middle_ready coeffs Q s hr.1.1 hr.1.2 hC hrow hord P hdata)
  exact hlast

theorem coordinate_ready (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0) (s : BasisState)
    (hs : BatchedPointReady s) {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hr : Single.Physical.tablePoint coeffs Q (tableAddressValue pointLookupAddress s) = .some hC)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    Ready coeffs Q (signedLookupCoordinateState
      (fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .x)
      (fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .y) s) := by
  let xs := fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .y
  let t := signedLookupCoordinateState xs ys s
  have ht : BatchedPointReady t := signedLookupCoordinateState_batchedReady xs ys s hs
  have haddr : tableAddressValue pointLookupAddress t = tableAddressValue pointLookupAddress s := by
    apply tableAddressValue_congr
    intro v hv
    apply signedLookupCoordinateState_frame xs ys s hs.1 v
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
    · simp only [pointLookupAddress,List.mem_range'_1] at hv
      simp only [List.mem_range'_1]
      omega
  have hz : t 854 = s 854 := signedLookupCoordinateState_sign xs ys s hs.1
  have hm : tableAddressValue pointLookupAddress (windowYNegateState t) % 16384 =
      tableAddressValue pointLookupAddress s % 16384 := by
    rw [windowYNegateState_address t ht.1.1,haddr]
  have hroute : rows (tree.routeLabel (windowYNegateState t)) =
      ⟨tableAddressValue pointLookupAddress s % 16384, by omega⟩ := by
    rw [rows_route]
    exact Fin.ext hm
  have hrow : constantPoint Q (coeffs (rows (tree.routeLabel (windowYNegateState t)))) =
      .some hC := by
    rw [hroute]
    exact (constantPoint_aliased coeffs Q ha _).trans hr
  have hx : xs (tableAddressValue pointLookupAddress s) = x.val := by
    simp [xs,hr,fieldValue,pointCoordinates]
  have hy : ys (tableAddressValue pointLookupAddress s) = y.val := by
    simp [ys,hr,fieldValue,pointCoordinates]
  have hyv : signedPointTableValue ys s = (if s 854 then y else -y).val := by
    unfold signedPointTableValue
    rw [hy]
    cases h : s 854
    · simp only [Bool.false_eq_true,if_false]
      exact (ZMod.neg_val' y).symm
    · simp only [if_true]
  have hd : pointStateCoordinates t =
      fig14EncodedEquiv x (if t 854 then y else -y) (fig14PointEncoding P) := by
    rw [hz]
    dsimp only [t]
    rw [signedLookupCoordinateState_eq xs ys s hs.1,hx,hyv]
    rw [fig14CoordinateState_encoded x (if s 854 then y else -y) s hs.1.1 hs.1.2,hP]
  exact ⟨ht,x,y,hC,hrow,hr ▸ Single.Physical.tablePoint_order coeffs Q hQ _,P,hd⟩

noncomputable def sources (coeffs : Fin 32768 → PointCoeff) (Q : Point) :
    List AdaptiveCircuit :=
  [signedLookupCoordinateProgram
    (fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .x)
    (fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .y),
    windowYNegate,source coeffs Q,windowYNegate]

theorem sources_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0) :
    CoherentlyImplementsOn (sequenceCircuit (sources coeffs Q))
      (Finsupp.lmapDomain ℂ ℂ (batchedState coeffs Q)) BatchedWindowValid := by
  let xs := fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .x
  let ys := fun a => fieldValue (Single.Physical.tablePoint coeffs Q a) .y
  have hfirst : CoherentlyImplementsOn (signedLookupCoordinateProgram xs ys)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupCoordinateState xs ys)) BatchedWindowValid :=
    restrictCoherent (signedLookupCoordinateProgram_coherent xs ys) (fun s hs => hs.1.1)
  have h := composeCoherent hfirst (signedSource_coherent coeffs Q) (by
    intro s hs
    obtain ⟨hs,P,hP⟩ := hs
    cases he : Single.Physical.tablePoint coeffs Q (tableAddressValue pointLookupAddress s) with
    | zero => exact False.elim (hn _ he)
    | some hC => exact coordinate_ready coeffs Q ha hQ s hs hC he P hP)
  simpa only [sources,sequenceCircuit,signedSource,adaptive_seq_assoc,adaptive_seq_done,
    batchedState,xs,ys] using h

theorem batchedState_valid (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (batchedState coeffs Q s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [batchedState_correct coeffs Q ha hQ hn s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

noncomputable def preparedState (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) : BasisState :=
  batchPrepareState (batchedState coeffs Q (batchPrepareState s))

theorem preparedState_correct (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    preparedState coeffs Q s = pointWrite
      (P + if s 854 then Single.Physical.tablePoint coeffs Q
          (tableAddressValue pointLookupAddress (batchPrepareState s))
        else -Single.Physical.tablePoint coeffs Q
          (tableAddressValue pointLookupAddress (batchPrepareState s))) s := by
  unfold preparedState
  rw [batchedState_correct coeffs Q ha hQ hn _ (batchPrepareState_ready s hs) P
    ((batchPrepareState_coordinates s).trans hP),batchPrepareState_pointWrite,
    batchPrepareState_involution,batchPrepareState_frame s 854 (by decide)]

attribute [local irreducible] batchPrepareState batchedState

theorem preparedSource_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0) :
    CoherentlyImplementsOn
      ((AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
        ((sequenceCircuit (sources coeffs Q)).seq
          (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done)))
      (Finsupp.lmapDomain ℂ ℂ (preparedState coeffs Q)) BatchedWindowValid := by
  have hc := composeCoherent (sources_coherent coeffs Q ha hQ hn)
    Single.Physical.batchPrepare_coherent (batchedState_valid coeffs Q ha hQ hn)
  have h := composeCoherent (f := batchPrepareState)
    (g := fun s => batchPrepareState (batchedState coeffs Q s))
    Single.Physical.batchPrepare_coherent hc batchPrepareState_valid
  exact h

def correctionProgram (start : Nat) :
    (count : Nat) × Straight 32768 start (start + count) :=
  ipxProgramOf rows tree path start

def segments : List (FixedSegment 32768) :=
  [coordinateProgram, yNegateProgram, correctionProgram, yNegateProgram]

def core (start : Nat) : (count : Nat) × Straight 32768 start (start + count) :=
  sequenceProgram 32768 segments start

def prepared (start : Nat) : (count : Nat) × Straight 32768 start (start + count) :=
  surroundCompiled (signedAddressCircuit 836 854 pointLookupAddress)
    (signedAddressCircuit 836 854 pointLookupAddress) (core start)

theorem correctionProgram_run (coeffs : Fin 32768 → PointCoeff) (start : Nat)
    (Q : Point) (history : Fin start → Bool) :
    compiledRun (correctionProgram start) (readConstant coeffs Q) history =
      (source coeffs Q).run := by
  simp only [correctionProgram,compiledRun,ipxProgramOf,lookupProgram_run,ipxOps_source,source]

theorem core_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (core start) (readConstant coeffs Q) history =
      (sequenceCircuit (sources coeffs Q)).run := by
  unfold core
  apply sequenceProgram_run
  unfold segments sources
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_
    (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h
    exact Single.Physical.coordinateProgram_run coeffs cursor Q h
  · intro cursor h
    exact yNegateProgram_run cursor _ h
  · intro cursor h
    exact correctionProgram_run coeffs cursor Q h
  · intro cursor h
    exact yNegateProgram_run cursor _ h

theorem prepared_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledRun (prepared start) (readConstant coeffs Q) history =
      ((AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
        ((sequenceCircuit (sources coeffs Q)).seq
          (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))).run := by
  unfold prepared
  exact surroundCompiled_run _ _ _ _ _ _ (core_run coeffs start Q history)

theorem correction_count (start : Nat) : (correctionProgram start).1 = 212979 := by
  simp only [correctionProgram,ipxProgramOf]
  rw [ipxOps_measurements _ _ _ tree_layout,ipxSchedule_queries,tree_nodes]

private theorem sequence_count (n : Nat) (ps : List (FixedSegment n)) (counts : List Nat)
    (h : List.Forall₂ (fun p count => ∀ start, (p start).1 = count) ps counts) (start : Nat) :
    (sequenceProgram n ps start).1 = counts.sum := by
  induction h generalizing start with
  | nil => simp only [sequenceProgram,List.sum_nil]
  | cons hp _ ih =>
    simp only [sequenceProgram,appendCompiled,List.sum_cons]
    rw [hp,ih]

theorem core_count (start : Nat) : (core start).1 = 30487725 := by
  have h := sequence_count 32768 segments
    ([30272702,1022,212979,1022] : List Nat) (by
      unfold segments
      exact List.Forall₂.cons Single.Physical.coordinate_count
        (List.Forall₂.cons Single.Physical.negate_count
          (List.Forall₂.cons correction_count
            (List.Forall₂.cons Single.Physical.negate_count .nil)))) start
  exact h

theorem prepared_count (start : Nat) : (prepared start).1 = 30487725 := by
  unfold prepared
  rw [surroundCompiled_count,core_count]

def actual : OuterWindow 32768 :=
  closedWindow (castFinish (by rw [prepared_count])
    (relabelStraight (windowAddressPerm 855 (by decide)) (prepared 0).2))

theorem actual_run (coeffs : Fin 32768 → PointCoeff) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((actual.program start).instantiate (readConstant coeffs Q) history).run =
      (((AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
        ((sequenceCircuit (sources coeffs Q)).seq
          (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))).relabel
            (windowAddressPerm 855 (by decide))).run := by
  unfold actual
  simp only [closedWindow_run,castFinish_instantiate,relabelStraight_instantiate,
    AdaptiveCircuit.run_relabel]
  have h := prepared_run coeffs 0 Q Fin.elim0
  unfold compiledRun at h
  exact congrArg (List.map (InstrumentBranch.relabel (windowAddressPerm 855 (by decide)))) h

noncomputable def actualState (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (s : BasisState) : BasisState :=
  relabelBasis (windowAddressPerm 855 (by decide))
    (preparedState coeffs Q (relabelBasis (windowAddressPerm 855 (by decide)).symm s))

private theorem point_bank_bound (w : Wire) (hw : w ∈ pointLogicalWires) : w < 839 := by
  simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hw
  dsimp only [Wire] at *
  omega

private theorem relabelPointWrite (start : Nat) (hs : 855 ≤ start) (P : Point)
    (s : BasisState) :
    relabelBasis (windowAddressPerm start hs)
      (pointWrite P (relabelBasis (windowAddressPerm start hs).symm s)) = pointWrite P s := by
  have hsym : (windowAddressPerm start hs).symm = windowAddressPerm start hs := rfl
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · have he := windowAddressPerm_core start hs w (point_bank_bound w hw)
    simp [relabelBasis,hsym,he,pointWrite,hw]
  · have hn : (windowAddressPerm start hs).symm w ∉ pointLogicalWires := by
      intro h
      have he := windowAddressPerm_core start hs _ (point_bank_bound _ h)
      rw [Equiv.apply_symm_apply] at he
      exact hw (he ▸ h)
    simp [relabelBasis,pointWrite,hw,hn]

private theorem relabelCoordinates (start : Nat) (hs : 855 ≤ start) (s : BasisState) :
    pointStateCoordinates (relabelBasis (windowAddressPerm start hs).symm s) =
      pointStateCoordinates s := by
  have he (bits : List Wire) (hb : ∀ w ∈ bits, w < 839) :
      wireValues bits (relabelBasis (windowAddressPerm start hs).symm s) = wireValues bits s := by
    apply List.map_congr_left
    intro w hw
    simp only [relabelBasis,Equiv.symm_symm,windowAddressPerm_core start hs w (hb w hw)]
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
  simp only [pointStateCoordinates,hx,hy,relabelBasis,Equiv.symm_symm,
    windowAddressPerm_core start hs 838 (by decide)]

theorem actual_coherent (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0)
    (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn ((actual.program start).instantiate (readConstant coeffs Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualState coeffs Q)) BatchedWindowValid := by
  have h := (preparedSource_coherent coeffs Q ha hQ hn).relabel
    (windowAddressPerm 855 (by decide))
  have hr : CoherentlyImplementsOn
      (((AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
        ((sequenceCircuit (sources coeffs Q)).seq
          (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))).relabel
            (windowAddressPerm 855 (by decide)))
      ((relabelState (windowAddressPerm 855 (by decide))).comp
        ((Finsupp.lmapDomain ℂ ℂ (preparedState coeffs Q)).comp
          (relabelState (windowAddressPerm 855 (by decide)).symm))) BatchedWindowValid := by
    obtain ⟨cs,hc,hm⟩ := h
    exact ⟨cs,hc.imp (fun _ _ hb s hs => hb s
      (Single.Physical.actualWindow_pullback_valid s hs)),hm⟩
  have he : CoherentlyImplementsOn
      (((AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done).seq
        ((sequenceCircuit (sources coeffs Q)).seq
          (AdaptiveCircuit.unitary (signedAddressCircuit 836 854 pointLookupAddress) .done))).relabel
            (windowAddressPerm 855 (by decide)))
      (Finsupp.lmapDomain ℂ ℂ (actualState coeffs Q)) BatchedWindowValid := by
    apply hr.congrIdeal
    intro s hs
    simp [actualState,LinearMap.comp_apply,relabelState,ket]
  unfold CoherentlyImplementsOn at he ⊢
  rw [actual_run coeffs start Q history]
  exact he

theorem actualState_selected (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedPointReady s) (P : Point)
    (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualState coeffs Q s = pointWrite
      (P + if s 870 then Single.Physical.tablePoint coeffs Q
          (signedTableAddress 32768 (windowRawDigit 0 s))
        else -Single.Physical.tablePoint coeffs Q
          (signedTableAddress 32768 (windowRawDigit 0 s))) s := by
  unfold actualState
  rw [preparedState_correct coeffs Q ha hQ hn _
    (Single.Physical.actualWindow_pullback_ready s hs) P
    ((relabelCoordinates 855 (by decide) s).trans hP),relabelPointWrite]
  have he : relabelBasis (windowAddressPerm 855 (by decide)).symm s 854 = s 870 := by
    simp only [relabelBasis,Equiv.symm_symm]
    exact congrArg s (windowAddressPerm_address 855 (by decide) 15 (by decide))
  rw [he,Single.Physical.actualWindow_selected_address s hs]

theorem actualState_valid (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) : BatchedWindowValid (actualState coeffs Q s) := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualState_selected coeffs Q ha hQ hn s hs P hP]
  exact ⟨pointWrite_batchedReady _ s hs,_,pointWrite_coordinates _ s⟩

theorem actualState_frame (coeffs : Fin 32768 → PointCoeff) (Q : Point)
    (ha : Aliased coeffs) (hQ : order • Q = 0)
    (hn : ∀ a, Single.Physical.tablePoint coeffs Q a ≠ 0)
    (s : BasisState) (hs : BatchedWindowValid s) (v : Wire) (hv : v ∉ pointLogicalWires) :
    actualState coeffs Q s v = s v := by
  obtain ⟨hs,P,hP⟩ := hs
  rw [actualState_selected coeffs Q ha hQ hn s hs P hP]
  simp [pointWrite,hv]

end ShorECDLP.Entrant.Lookup15Scratch
