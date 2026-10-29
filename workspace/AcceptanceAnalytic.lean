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
