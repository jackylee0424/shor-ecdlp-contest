import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.StateModel
import ShorECDLP.Submission.«2607_13816».OrderFinding.PointEigenstates

namespace ShorECDLP.FlagCorrection

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
attribute [local irreducible] flagCorrectionState
attribute [local irreducible] ShorECDLP.Paper2607_13816.pointWrite

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

theorem pointLookupValid_flagDomain (st : BasisState) (hs : PointLookupValid st) :
    FlagDomain st := by
  refine ⟨⟨?_, ?_, ?_⟩, hs.2⟩
  · intro w hw
    apply hs.1.1 w
    apply List.mem_append_right
    simp only [pointLookupPath, List.mem_range'] at hw
    simp only [List.mem_range']
    obtain ⟨i, hi, rfl⟩ := hw
    exact ⟨i, by omega, by omega⟩
  · intro w hw
    apply hs.1.1 w
    apply List.mem_append_left
    simp only [halfScratch, List.mem_range'] at hw
    simp only [List.mem_range']
    obtain ⟨i, hi, rfl⟩ := hw
    exact ⟨4 + i, by omega, by omega⟩
  · apply hs.1.1 halfFlag
    apply List.mem_append_left
    simp [halfFlag]

theorem pointLookupValid_flags_zero (st : BasisState) (hs : PointLookupValid st) (k : Fin 4) :
    st k.val = false := by
  apply hs.1.1 k.val
  apply List.mem_append_left
  simp only [List.mem_range']
  exact ⟨k.val, by omega, by omega⟩

theorem flagCorrectionState_finite {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (st : BasisState) (hs : FlagDomain st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (batchWindowTree.routeLabel st))) = .some hC)
    (horder : order • (.some hC : Point) = 0) (hC0 : (.some hC : Point) ≠ 0)
    (k : Fin 4)
    (hdata : (stateFlagModel st).data = endpointSource x y (.some hC) k)
    (hflags : (stateFlagModel st).flags = fun _ => false) :
    let out := flagCorrectionState (readConstant coeffs Q) rows st
    (stateFlagModel out).data = endpointTarget (.some hC) k ∧
      (stateFlagModel out).flags = fun _ => false := by
  dsimp only
  have hwords : stateEndpointWords coeffs Q rows st =
      modelWords (endpointSource x y (.some hC)) (endpointTarget (.some hC)) := by
    exact normalizedEndpointWords_eq_model coeffs Q _ hC hrow
  have hE := exceptionInputAt_injective (.some hC) horder hC0
  have hF := endpointSource_injective x y (.some hC) hE
  have hT := endpointTarget_injective (.some hC) hE
  have hm0 : stateFlagModel st = initialFlagModel (endpointSource x y (.some hC) k) := by
    apply FlagModel.ext
    · exact hdata
    · exact hflags
  have hm := flagCorrectionState_model coeffs Q rows st hs
  rw [hwords, hm0] at hm
  have hr := runFlagModel_source hF hT k
  rw [hm]
  exact hr

theorem fixedExceptionInputs_exists (C P : Point) (h : P ∈ fixedExceptionInputs C) :
    ∃ k : Fin 4, exceptionInputAt C k = P := by
  have hm : P = 0 ∨ P = C ∨ P = -C ∨ P = -(C + C) := by
    simpa [fixedExceptionInputs] using h
  rcases hm with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

theorem exceptionInputAt_mem_fixed (C : Point) (k : Fin 4) :
    exceptionInputAt C k ∈ fixedExceptionInputs C := by
  fin_cases k <;> simp [exceptionInputAt, fixedExceptionInputs]

theorem flagCorrectionState_nonexceptional {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (rows : Nat → Fin n) (st : BasisState) (hs : FlagDomain st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (batchWindowTree.routeLabel st))) = .some hC)
    (P : Point) (hP : P ∉ fixedExceptionInputs (.some hC))
    (hdata : (stateFlagModel st).data =
      coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)))
    (hflags : (stateFlagModel st).flags = fun _ => false) :
    let out := flagCorrectionState (readConstant coeffs Q) rows st
    (stateFlagModel out).data =
        coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P)) ∧
      (stateFlagModel out).flags = fun _ => false := by
  dsimp only
  let data := coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding P))
  let F := endpointSource x y (.some hC)
  let T := endpointTarget (.some hC)
  have hwords : stateEndpointWords coeffs Q rows st = modelWords F T := by
    exact normalizedEndpointWords_eq_model coeffs Q _ hC hrow
  have hSinj : Function.Injective
      (fun R : Point => coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding R))) :=
    coordinateWordBits_injective.comp
      ((fig14EncodedEquiv x y).injective.comp fig14PointEncoding_injective)
  have hTinj : Function.Injective
      (fun R : Point => coordinateWordBits (fig14PointEncoding (R + (.some hC : Point)))) := by
    intro A B h
    exact add_right_cancel (fig14PointEncoding_injective (coordinateWordBits_injective h))
  have hF : ∀ k, data ≠ F k := by
    intro k he
    have heq : P = exceptionInputAt (.some hC) k := hSinj
      (by simpa [data, F, endpointSource] using he)
    exact hP (heq.symm ▸ exceptionInputAt_mem_fixed (.some hC) k)
  have hnon : fig14EncodedEquiv x y (fig14PointEncoding P) =
      fig14PointEncoding (P + .some hC) :=
    fig14EncodedEquiv_nonexceptional hC P
      (by simpa [fixedExceptionInputs, fig14ExceptionalPoints] using hP)
  have hgood : data = coordinateWordBits (fig14PointEncoding (P + .some hC)) := by
    exact congrArg coordinateWordBits hnon
  have hT : ∀ k, data ≠ T k := by
    intro k he
    have := hgood.symm.trans he
    have heq : P = exceptionInputAt (.some hC) k := hTinj
      (by simpa [T, endpointTarget] using this)
    exact hP (heq.symm ▸ exceptionInputAt_mem_fixed (.some hC) k)
  have hm0 : stateFlagModel st = initialFlagModel data := by
    apply FlagModel.ext
    · exact hdata
    · exact hflags
  have hm := flagCorrectionState_model coeffs Q rows st hs
  rw [hwords, hm0] at hm
  have hr := runFlagModel_unmatched data hF hT
  rw [hm, hr]
  exact ⟨rfl, rfl⟩

theorem flagCorrectionState_eq_pointWrite_data {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (rows : Nat → Fin n) (st : BasisState) (hs : PointLookupValid st)
    (R : Point)
    (hdataOut : (stateFlagModel
      (flagCorrectionState (readConstant coeffs Q) rows st)).data =
        coordinateWordBits (fig14PointEncoding R))
    (hflagsOut : (stateFlagModel
      (flagCorrectionState (readConstant coeffs Q) rows st)).flags = fun _ => false) :
    flagCorrectionState (readConstant coeffs Q) rows st = pointWrite R st := by
  let out := flagCorrectionState (readConstant coeffs Q) rows st
  have hdomain := pointLookupValid_flagDomain st hs
  have hpwValid := pointWrite_valid R st hs.1
  have hpwPort := accumulatorPort_coordinates (pointWrite R st) hpwValid
  rw [pointWrite_coordinates] at hpwPort
  have hacc : out ∘ accumulatorPort = pointWrite R st ∘ accumulatorPort := by
    change (stateFlagModel out).data = pointWrite R st ∘ accumulatorPort
    rw [hdataOut]
    exact hpwPort.symm
  funext w
  by_cases hw : w ∈ pointLogicalWires
  · rw [← accumulatorPort_list] at hw
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hw
    rw [← hi]
    exact congrFun hacc i
  · rw [pointWrite_frame R st w hw]
    by_cases hlow : w < 4
    · let j : Fin 4 := ⟨w, hlow⟩
      have ho := congrFun hflagsOut j
      have hz := pointLookupValid_flags_zero st hs j
      change out w = false at ho
      change st w = false at hz
      exact ho.trans hz.symm
    · apply flagCorrectionState_frame (readConstant coeffs Q) rows st hdomain w
        (Nat.le_of_not_gt hlow)
      intro i he
      apply hw
      rw [← accumulatorPort_list]
      exact List.mem_ofFn.mpr ⟨i, he.symm⟩

theorem flagCorrectionState_eq_pointWrite {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (rows : Nat → Fin n) (st : BasisState) (hs : PointLookupValid st)
    (C P : Point) (k : Fin 4) (hkP : exceptionInputAt C k = P)
    (hdataOut : (stateFlagModel
      (flagCorrectionState (readConstant coeffs Q) rows st)).data = endpointTarget C k)
    (hflagsOut : (stateFlagModel
      (flagCorrectionState (readConstant coeffs Q) rows st)).flags = fun _ => false) :
    flagCorrectionState (readConstant coeffs Q) rows st = pointWrite (P + C) st := by
  apply flagCorrectionState_eq_pointWrite_data coeffs Q rows st hs (P + C)
  · rw [hdataOut]
    unfold endpointTarget
    exact congrArg (fun R => coordinateWordBits (fig14PointEncoding (R + C))) hkP
  · exact hflagsOut

theorem flagCorrectionState_coordinates {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (st : BasisState) (hs : PointLookupValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (batchWindowTree.routeLabel st))) = .some hC)
    (horder : order • (.some hC : Point) = 0) (hC0 : (.some hC : Point) ≠ 0)
    (P : Point)
    (hdata : pointStateCoordinates st =
      fig14EncodedEquiv x y (fig14PointEncoding P))
    (hk : P ∈ fixedExceptionInputs (.some hC)) :
    let out := flagCorrectionState (readConstant coeffs Q) rows st
    pointStateCoordinates out = fig14PointEncoding (P + .some hC) ∧
      (stateFlagModel out).flags = fun _ => false := by
  dsimp only
  have hdomain := pointLookupValid_flagDomain st hs
  have hport := accumulatorPort_coordinates st hs.1
  rw [hdata] at hport
  obtain ⟨k, hkP⟩ := fixedExceptionInputs_exists (.some hC) P hk
  have hmodel := flagCorrectionState_finite coeffs Q rows st hdomain hC hrow horder hC0 k
    (by simpa [stateFlagModel, endpointSource, hkP] using hport)
    (by funext j; exact pointLookupValid_flags_zero st hs j)
  dsimp only at hmodel
  have hout := flagCorrectionState_eq_pointWrite coeffs Q rows st hs (.some hC) P k hkP
    hmodel.1 hmodel.2
  constructor
  · rw [hout, pointWrite_coordinates]
  · exact hmodel.2

theorem flagCorrectionState_coordinates_all {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (rows : Nat → Fin n) (st : BasisState) (hs : PointLookupValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (batchWindowTree.routeLabel st))) = .some hC)
    (horder : order • (.some hC : Point) = 0) (hC0 : (.some hC : Point) ≠ 0)
    (P : Point)
    (hdata : pointStateCoordinates st =
      fig14EncodedEquiv x y (fig14PointEncoding P)) :
    let out := flagCorrectionState (readConstant coeffs Q) rows st
    pointStateCoordinates out = fig14PointEncoding (P + .some hC) ∧
      (stateFlagModel out).flags = fun _ => false := by
  by_cases hk : P ∈ fixedExceptionInputs (.some hC)
  · exact flagCorrectionState_coordinates coeffs Q rows st hs hC hrow horder hC0 P hdata hk
  · dsimp only
    have hdomain := pointLookupValid_flagDomain st hs
    have hport := accumulatorPort_coordinates st hs.1
    rw [hdata] at hport
    have hmodel := flagCorrectionState_nonexceptional coeffs Q rows st hdomain hC hrow P hk
      (by simpa [stateFlagModel] using hport)
      (by funext j; exact pointLookupValid_flags_zero st hs j)
    dsimp only at hmodel
    have hnon : fig14EncodedEquiv x y (fig14PointEncoding P) =
        fig14PointEncoding (P + .some hC) :=
      fig14EncodedEquiv_nonexceptional hC P
        (by simpa [fixedExceptionInputs, fig14ExceptionalPoints] using hk)
    have houtData : (stateFlagModel
        (flagCorrectionState (readConstant coeffs Q) rows st)).data =
        coordinateWordBits (fig14PointEncoding (P + .some hC)) :=
      hmodel.1.trans (congrArg coordinateWordBits hnon)
    have hout := flagCorrectionState_eq_pointWrite_data coeffs Q rows st hs
      (P + .some hC) houtData hmodel.2
    constructor
    · rw [hout, pointWrite_coordinates]
    · exact hmodel.2

theorem flagCorrectionState_pointWrite_exceptional {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (rows : Nat → Fin n) (st : BasisState) (hs : PointLookupValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (batchWindowTree.routeLabel st))) = .some hC)
    (horder : order • (.some hC : Point) = 0) (hC0 : (.some hC : Point) ≠ 0)
    (P : Point)
    (hdata : pointStateCoordinates st = fig14EncodedEquiv x y (fig14PointEncoding P))
    (hk : P ∈ fixedExceptionInputs (.some hC)) :
    let out := flagCorrectionState (readConstant coeffs Q) rows st
    out = pointWrite (P + .some hC) st ∧
      (stateFlagModel out).flags = fun _ => false := by
  dsimp only
  have hdomain := pointLookupValid_flagDomain st hs
  have hport := accumulatorPort_coordinates st hs.1
  rw [hdata] at hport
  obtain ⟨k, hkP⟩ := fixedExceptionInputs_exists (.some hC) P hk
  have hmodel := flagCorrectionState_finite coeffs Q rows st hdomain hC hrow horder hC0 k
    (by simpa [stateFlagModel, endpointSource, hkP] using hport)
    (by funext j; exact pointLookupValid_flags_zero st hs j)
  dsimp only at hmodel
  have hout : flagCorrectionState (readConstant coeffs Q) rows st =
      pointWrite (P + .some hC) st :=
    flagCorrectionState_eq_pointWrite coeffs Q rows st hs (.some hC) P k hkP
      hmodel.1 hmodel.2
  exact And.intro hout hmodel.2

theorem flagCorrectionState_pointWrite_nonexceptional {n : Nat}
    (coeffs : Fin n → PointCoeff) (Q : Point) (rows : Nat → Fin n)
    (st : BasisState) (hs : PointLookupValid st) {x y : Fp}
    (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (batchWindowTree.routeLabel st))) = .some hC)
    (P : Point) (hdata : pointStateCoordinates st =
      fig14EncodedEquiv x y (fig14PointEncoding P))
    (hk : P ∉ fixedExceptionInputs (.some hC)) :
    let out := flagCorrectionState (readConstant coeffs Q) rows st
    out = pointWrite (P + .some hC) st ∧
      (stateFlagModel out).flags = fun _ => false := by
  dsimp only
  have hdomain := pointLookupValid_flagDomain st hs
  have hport := accumulatorPort_coordinates st hs.1
  rw [hdata] at hport
  have hmodel := flagCorrectionState_nonexceptional coeffs Q rows st hdomain hC hrow P hk
    (by simpa [stateFlagModel] using hport)
    (by funext j; exact pointLookupValid_flags_zero st hs j)
  dsimp only at hmodel
  have hnon : fig14EncodedEquiv x y (fig14PointEncoding P) =
      fig14PointEncoding (P + .some hC) :=
    fig14EncodedEquiv_nonexceptional hC P
      (by simpa [fixedExceptionInputs, fig14ExceptionalPoints] using hk)
  have houtData : (stateFlagModel
      (flagCorrectionState (readConstant coeffs Q) rows st)).data =
      coordinateWordBits (fig14PointEncoding (P + .some hC)) :=
    hmodel.1.trans (congrArg coordinateWordBits hnon)
  have hout : flagCorrectionState (readConstant coeffs Q) rows st =
      pointWrite (P + .some hC) st :=
    flagCorrectionState_eq_pointWrite_data coeffs Q rows st hs
      (P + .some hC) houtData hmodel.2
  exact And.intro hout hmodel.2

theorem flagCorrectionState_pointWrite_all {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (rows : Nat → Fin n) (st : BasisState) (hs : PointLookupValid st)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs (rows (batchWindowTree.routeLabel st))) = .some hC)
    (horder : order • (.some hC : Point) = 0) (hC0 : (.some hC : Point) ≠ 0)
    (P : Point) (hdata : pointStateCoordinates st =
      fig14EncodedEquiv x y (fig14PointEncoding P)) :
    let out := flagCorrectionState (readConstant coeffs Q) rows st
    out = pointWrite (P + .some hC) st ∧
      (stateFlagModel out).flags = fun _ => false := by
  by_cases hk : P ∈ fixedExceptionInputs (.some hC)
  · exact flagCorrectionState_pointWrite_exceptional coeffs Q rows st hs hC hrow horder hC0
      P hdata hk
  · exact flagCorrectionState_pointWrite_nonexceptional coeffs Q rows st hs hC hrow P hdata hk

end ShorECDLP.FlagCorrection
