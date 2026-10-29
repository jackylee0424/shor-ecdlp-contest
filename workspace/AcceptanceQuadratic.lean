import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedCoverage
import Mathlib.Tactic

open scoped BigOperators
open ShorECDLP.Quantum.PhaseEstimation
namespace ShorECDLP.Acceptance
noncomputable section

lemma sum_range_first (N : ℕ) :
    ∑ x ∈ Finset.range N, (x:ℝ) = (N:ℝ)*((N:ℝ)-1)/2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_range_second (N : ℕ) :
    ∑ x ∈ Finset.range N, (x:ℝ)^2 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_quadratic (N : ℕ) (a b c : ℝ) :
    ∑ x ∈ Finset.range N, (a*(x:ℝ)^2+b*(x:ℝ)+c) =
      a*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6) + b*((N:ℝ)*((N:ℝ)-1)/2) + (N:ℝ)*c := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_range_first, sum_range_second,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma sum_range_difference_sq (N : ℕ) :
    ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^2 =
      (N:ℝ)^2*((N:ℝ)^2-1)/6 := by
  simp_rw [show ∀ x y : ℕ, ((x:ℝ)-(y:ℝ))^2 =
      1*(y:ℝ)^2+(-2*(x:ℝ))*(y:ℝ)+(x:ℝ)^2 by intros; ring,
    sum_quadratic]
  trans ∑ x ∈ Finset.range N,
      ((N:ℝ)*(x:ℝ)^2 + (-((N:ℝ)*((N:ℝ)-1)))*(x:ℝ) +
        ((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6))
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_quadratic]; ring

lemma eigen_mul_conj (t : ℝ) (x y : ℕ) :
    (eigenvalue t ^ x * star (eigenvalue t ^ y)).re =
      Real.cos (2*Real.pi*t*((x:ℝ)-(y:ℝ))) := by
  rw [eigenvalue_pow_eq_eigenvalue_mul, eigenvalue_pow_eq_eigenvalue_mul]
  simp only [eigenvalue, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  rw [Complex.exp_re]
  simp
  congr 1
  ring

lemma geometric_normSq (N : ℕ) (t : ℝ) :
    Complex.normSq (((N:ℂ)⁻¹) * ∑ x ∈ Finset.range N, eigenvalue t ^ x) =
      (N:ℝ)⁻¹^2 * ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
        Real.cos (2*Real.pi*t*((x:ℝ)-(y:ℝ))) := by
  rw [Complex.normSq_mul]
  have hs (z : ℂ) : Complex.normSq z = (z * star z).re := by
    simp [Complex.mul_conj]
  rw [hs (∑ x ∈ Finset.range N, eigenvalue t ^ x)]
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum,
    eigen_mul_conj]
  simp only [Complex.normSq_inv, Complex.normSq_natCast, ← inv_pow]
  rw [Finset.sum_comm]
  simp only [inv_pow, pow_two]
  ring

/-- A quadratic lower bound for the exact finite Fourier peak. -/
theorem geometric_quadratic (N : ℕ) (hN : 0 < N) (t : ℝ) :
    1 - Real.pi^2 * ((N:ℝ)*t)^2 / 3 ≤
      Complex.normSq (((N:ℂ)⁻¹) * ∑ x ∈ Finset.range N, eigenvalue t ^ x) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [geometric_normSq]
  have hb := Finset.sum_le_sum (s := Finset.range N) (fun x hx =>
    Finset.sum_le_sum (s := Finset.range N) (fun y hy =>
      Real.one_sub_sq_div_two_le_cos (x := 2*Real.pi*t*((x:ℝ)-(y:ℝ)))))
  have hid : (∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
      (1 - (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2)) =
      (N:ℝ)^2 - 2*Real.pi^2*t^2*((N:ℝ)^2*((N:ℝ)^2-1)/6) := by
    simp_rw [show ∀ x y : ℕ, (1 - (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2) =
        1 - (2*Real.pi^2*t^2)*((x:ℝ)-(y:ℝ))^2 by intros; ring,
      Finset.sum_sub_distrib, ← Finset.mul_sum, sum_range_difference_sq]
    simp
    ring
  rw [hid] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (N:ℝ)⁻¹)
  have he : (N:ℝ)⁻¹^2 * ((N:ℝ)^2 - 2*Real.pi^2*t^2*((N:ℝ)^2*((N:ℝ)^2-1)/6)) =
      1 - Real.pi^2*((N:ℝ)*t)^2/3 + Real.pi^2*t^2/3 := by
    field_simp
    <;> ring
  rw [he] at hb'
  nlinarith [sq_nonneg (Real.pi*t)]
end
end ShorECDLP.Acceptance

open scoped BigOperators
namespace ShorECDLP.Acceptance
noncomputable section
open ShorECDLP.Paper2607_13816

/-- Index the centered residues without an integer interval. -/
def residualIndex (r N : ℕ) (k : Fin r) : Fin r :=
  ⟨(N*k.val+r/2)%r, Nat.mod_lt _ (by have := k.isLt; omega)⟩

lemma residualIndex_bijective (r N : ℕ) [Fact (Nat.Prime r)]
    (hN : (N : ZMod r) ≠ 0) : Function.Bijective (residualIndex r N) := by
  have hr := (Fact.out : Nat.Prime r).pos
  have hi : Function.Injective (residualIndex r N) := by
    intro a b hab
    apply Fin.ext
    have he : (N:ZMod r) * (a.val:ZMod r) + (r/2:ℕ) =
        (N:ZMod r) * (b.val:ZMod r) + (r/2:ℕ) := by
      have := congrArg (fun j : Fin r => (j.val:ZMod r)) hab
      simpa [residualIndex, Nat.cast_add, Nat.cast_mul] using this
    have he' := mul_left_cancel₀ hN (add_right_cancel he)
    have := congrArg ZMod.val he'
    simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using this
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, rfl⟩

lemma raw_round_eq (r n : ℕ) (k : Fin r) (hodd : r%2=1) :
    reducedPeakRaw r n k = (2^n*k.val+r/2)/r := by
  have hr : 0 < r := by have := k.isLt; omega
  have he := Nat.mod_add_div r 2
  have h1 := Nat.div_mul_le_self (2^n*k.val+r/2) r
  have h2 := Nat.lt_mul_div_succ (2^n*k.val+r/2) hr
  apply (Nat.div_eq_of_lt_le ?_ ?_)
  · nlinarith
  · nlinarith

lemma raw_residual (r n : ℕ) (k : Fin r) (hodd : r%2=1) :
    (2^n:ℕ)*(k.val:ℝ)/(r:ℝ) - (reducedPeakRaw r n k:ℝ) =
      ((residualIndex r (2^n) k).val-(r/2:ℕ):ℝ)/(r:ℝ) := by
  have hr : (r:ℝ) ≠ 0 := by have := k.isLt; exact_mod_cast (by omega : r ≠ 0)
  rw [raw_round_eq r n k hodd]
  have he := Nat.mod_add_div (2^n*k.val+r/2) r
  have heR : (((2^n*k.val+r/2)%r:ℕ):ℝ) + (r:ℝ)*(((2^n*k.val+r/2)/r:ℕ):ℝ) =
      (2^n:ℕ)*(k.val:ℝ)+(r/2:ℕ) := by exact_mod_cast he
  dsimp [residualIndex]
  field_simp
  nlinarith

lemma centered_second (r : ℕ) (hodd : r%2=1) :
    ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^2 = (r:ℝ)*((r:ℝ)^2-1)/12 := by
  change (∑ k : Fin r, (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^2) k.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^2) r]
  have he : (r:ℝ) = 2*(r/2:ℕ)+1 := by
    have := Nat.mod_add_div r 2
    exact_mod_cast (by omega : r = 2*(r/2)+1)
  trans ∑ x ∈ Finset.range r, (1*(x:ℝ)^2+(-2*(r/2:ℕ))*(x:ℝ)+(r/2:ℕ)^2)
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_quadratic, he]; ring

end
end ShorECDLP.Acceptance

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
  convert h using 1 <;> ring

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
    (hodd : r%2=1) (hN : (2^n:ℕ) ≠ 0) (hNz : ((2^n:ℕ):ZMod r) ≠ 0) :
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
    <;> ring
  rw [hid] at hb
  exact le_trans (le_add_of_nonneg_right (by positivity)) hb
end
end ShorECDLP.Acceptance

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