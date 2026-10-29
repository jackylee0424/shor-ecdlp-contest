namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

lemma characterProduct_bijective (r d : ℕ) [Fact (Nat.Prime r)]
    (hd : (d:ZMod r) ≠ 0) : Function.Bijective (paperCharacterProduct d : Fin r → Fin r) := by
  have hi : Function.Injective (paperCharacterProduct d : Fin r → Fin r) := by
    intro a b hab
    apply Fin.ext
    have he : (d:ZMod r)*(a.val:ZMod r) = (d:ZMod r)*(b.val:ZMod r) := by
      have := congrArg (fun j : Fin r => (j.val:ZMod r)) hab
      simpa [paperCharacterProduct, Nat.cast_mul] using this
    have he' := mul_left_cancel₀ hd he
    have := congrArg ZMod.val he'
    simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using this
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,rfl⟩

/-- Keep each nonzero character's own peak contribution, with its exact weight. -/
lemma coverage_exact_peak_lower (r n m d : ℕ) [Fact (Nat.Prime r)]
    (hn : r < 2^n) :
    (1/(r:ℝ)) * ∑ k ∈ (Finset.univ.erase (⟨0,(Fact.out : Nat.Prime r).pos⟩ : Fin r)),
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val) *
      Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
        (reducedPeak r m (paperCharacterProduct d k)).val) ≤ reducedCoverageMass r n m d := by
  classical
  let S := Finset.univ.erase (⟨0,(Fact.out : Nat.Prime r).pos⟩ : Fin r)
  let peak := asymmetricPairPeak r n m d hn
  let f : (Fin (2^n) × Fin (2^m)) → ℝ := fun out =>
    if (d:ZMod r) ∈ reducedShiftCandidates r n m out
      then asymmetricPairMass r n m d out else 0
  have hf : ∀ out, 0 ≤ f out := by
    intro out; dsimp [f]; split
    · exact asymmetricPairMass_nonneg _ _ _ _ _
    · rfl
  have hp (k : Fin r) (hk : k ∈ S) :
      (1/(r:ℝ)) * (Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val) *
      Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
        (reducedPeak r m (paperCharacterProduct d k)).val)) ≤ f (peak k) := by
    have hkz : (k.val:ZMod r) ≠ 0 := by
      intro hz
      have hv := congrArg ZMod.val hz
      have hk0 : k ≠ ⟨0,(Fact.out : Nat.Prime r).pos⟩ := (Finset.mem_erase.mp hk).1
      apply hk0; apply Fin.ext
      simpa [ZMod.val_natCast_of_lt k.isLt] using hv
    dsimp [f,peak]
    have hm : (d:ZMod r) ∈ reducedShiftCandidates r n m (asymmetricPairPeak r n m d hn k) :=
      reducedShiftCandidates_correct r n m d hn k hkz
    rw [if_pos hm]
    unfold asymmetricPairMass
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum
      (f := fun i : Fin r =>
        Complex.normSq (paperPhaseAmplitude n ((i.val:ℝ)/r) (paperPeak r n hn k).val) *
        Complex.normSq (paperPhaseAmplitude m ((((d*i.val)%r:ℕ):ℝ)/r)
          (reducedPeak r m (paperCharacterProduct d k)).val))
      (fun i _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) (Finset.mem_univ k)
  calc
    _ = ∑ k ∈ S, (1/(r:ℝ)) *
        (Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val) *
        Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
          (reducedPeak r m (paperCharacterProduct d k)).val)) := Finset.mul_sum ..
    _ ≤ ∑ k ∈ S, f (peak k) := Finset.sum_le_sum hp
    _ = ∑ out ∈ S.image peak, f out := by
      rw [Finset.sum_image]
      intro k _ l _ he
      exact asymmetricPairPeak_injective r n m d hn he
    _ ≤ ∑ out, f out := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun out _ _ => hf out)
    _ = reducedCoverageMass r n m d := rfl

/-- Uniform in the correlation between the two residual marginals. -/
theorem coverage_quadratic (r n m d : ℕ) [Fact (Nat.Prime r)]
    (hn : r < 2^n) (hodd : r%2=1)
    (hN : ((2^n:ℕ):ZMod r) ≠ 0) (hM : ((2^m:ℕ):ZMod r) ≠ 0)
    (hd : (d:ZMod r) ≠ 0) :
    1 - Real.pi^2/18 - 1/(r:ℝ) ≤ reducedCoverageMass r n m d := by
  classical
  have hr := (Fact.out : Nat.Prime r).pos
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  let z : Fin r := ⟨0,hr⟩
  let u (k : Fin r) := Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (paperPeak r n hn k).val)
  let v (k : Fin r) := Complex.normSq (paperPhaseAmplitude m (((paperCharacterProduct d k).val:ℝ)/r)
    (reducedPeak r m (paperCharacterProduct d k)).val)
  have hu (k : Fin r) : u k ≤ 1 := peak_mass_le_one _ _ _
  have hv (k : Fin r) : v k ≤ 1 := peak_mass_le_one _ _ _
  have hp (k : Fin r) : u k + v k - 1 ≤ u k * v k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hu k)) (sub_nonneg.mpr (hv k))]
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase z) (fun k hk => hp k)
  have he := Finset.sum_erase_add Finset.univ (fun k => u k+v k-1) (Finset.mem_univ z)
  have hz : u z+v z-1 ≤ 1 := by linarith [hu z,hv z]
  have huSum : (r:ℝ)*(1-Real.pi^2/36) ≤ ∑ k, u k := by
    simpa [u, paper_reduced_eq] using average_peak_quadratic r n hodd (by positivity) hN
  have hvSum : (r:ℝ)*(1-Real.pi^2/36) ≤ ∑ k, v k := by
    have heq := (characterProduct_bijective r d hd).sum_comp
      (fun k => Complex.normSq (paperPhaseAmplitude m ((k.val:ℝ)/r) (reducedPeak r m k).val))
    dsimp [v]
    rw [heq]
    exact average_peak_quadratic r m hodd (by positivity) hM
  have hl : (r:ℝ)*(1-Real.pi^2/18)-1 ≤ ∑ k ∈ Finset.univ.erase z, u k*v k := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at he hsum
    linarith
  have hb := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 1/(r:ℝ))
  have hi : (1/(r:ℝ))*((r:ℝ)*(1-Real.pi^2/18)-1) = 1-Real.pi^2/18-1/(r:ℝ) := by
    field_simp
  rw [hi] at hb
  exact hb.trans (coverage_exact_peak_lower r n m d hn)

end
end ShorECDLP.Acceptance
