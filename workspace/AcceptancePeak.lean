-- Combined by workspace/acceptance_check.py after AcceptanceAnalytic/Residues.
namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

lemma raw_peak_quadratic (r n : ℕ) (k : Fin r) (hodd : r%2=1) :
    1 - Real.pi^2 * (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 / (3*(r:ℝ)^2) ≤
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) := by
  have h := geometric_quadratic (2^n) (by positivity)
    ((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ))
  change _ ≤ Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) at h
  have hN : ((2^n:ℕ):ℝ) ≠ 0 := by positivity
  have he : ((2^n:ℕ):ℝ)*((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ)) =
      (2^n:ℕ)*(k.val:ℝ)/r - (reducedPeakRaw r n k:ℝ) := by field_simp
  rw [he, raw_residual r n k hodd] at h
  convert h using 1 ; ring

lemma raw_reduced_mass_eq (r n : ℕ) (k : Fin r) :
    Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) =
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
  have hle := reducedPeakRaw_le r n k
  by_cases heq : reducedPeakRaw r n k = 2^n
  · have hp (t : ℝ) : eigenvalue (t-1)=eigenvalue t := by
      unfold eigenvalue
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-1, ?_⟩
      push_cast
      ring
    simp [reducedPeak, heq, paperPhaseAmplitude, hp]
  · simp [reducedPeak, Nat.mod_eq_of_lt (by omega : reducedPeakRaw r n k < 2^n)]

lemma paper_reduced_eq (r n : ℕ) (hn : r < 2^n) (k : Fin r) :
    paperPeak r n hn k = reducedPeak r n k := by
  apply Fin.ext
  dsimp [paperPeak, reducedPeak, reducedPeakRaw]
  exact (Nat.mod_eq_of_lt (paperPeak r n hn k).isLt).symm

lemma peak_mass_le_one (n : ℕ) (t : ℝ) (v : Fin (2^n)) :
    Complex.normSq (paperPhaseAmplitude n t v.val) ≤ 1 := by
  rw [← paperPhaseAmplitude_totalMass t n]
  exact Finset.single_le_sum (fun (i : Fin (2^n)) _ => Complex.normSq_nonneg (paperPhaseAmplitude n t i.val)) (Finset.mem_univ v)

lemma average_peak_quadratic (r n : ℕ) [Fact (Nat.Prime r)]
    (hodd : r%2=1) (_hN : (2^n:ℕ) ≠ 0) (hNz : ((2^n:ℕ):ZMod r) ≠ 0) :
    (r:ℝ)*(1-Real.pi^2/36) ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
  have hr := (Fact.out : Nat.Prime r).pos
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun k hk =>
    (raw_peak_quadratic r n k hodd).trans_eq (raw_reduced_mass_eq r n k))
  have he : ∑ k : Fin r, (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 =
      (r:ℝ)*((r:ℝ)^2-1)/12 := by
    calc
      _ = ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^2 := by
        exact (residualIndex_bijective r (2^n) hNz).sum_comp (fun k => ((k.val:ℝ)-(r/2:ℕ))^2)
      _ = _ := centered_second r hodd
  simp_rw [show ∀ k : Fin r,
    1 - Real.pi^2 * (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 / (3*(r:ℝ)^2) =
    1 - (Real.pi^2/(3*(r:ℝ)^2)) * (((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))^2 by intro; ring,
    Finset.sum_sub_distrib, ← Finset.mul_sum, he,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hb
  have hid : (r:ℝ) - Real.pi^2/(3*(r:ℝ)^2)*((r:ℝ)*((r:ℝ)^2-1)/12) =
      (r:ℝ)*(1-Real.pi^2/36) + Real.pi^2/(36*(r:ℝ)) := by
    field_simp
    ; ring
  rw [hid] at hb
  exact le_trans (le_add_of_nonneg_right (by positivity)) hb
end
end ShorECDLP.Acceptance
