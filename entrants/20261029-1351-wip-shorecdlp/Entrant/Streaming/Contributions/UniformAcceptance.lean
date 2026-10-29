import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedCoverage
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import ShorECDLP.Submission.«2607_13816».Window.RawDistribution

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
  simp only [Complex.normSq_inv, Complex.normSq_natCast]
  rw [Finset.sum_comm]
  simp only [pow_two]
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
    ; ring
  rw [he] at hb'
  nlinarith [sq_nonneg (Real.pi*t)]
end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
noncomputable section

lemma primitive_nonneg (f f' : ℝ → ℝ) (hf : ∀ x, HasDerivAt f (f' x) x)
    (h0 : 0 ≤ f 0) (hd : ∀ x, 0 ≤ x → 0 ≤ f' x) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · exact fun y hy => (hf y).continuousAt.continuousWithinAt
    · exact fun y hy => (hf y).hasDerivWithinAt
    · exact fun y hy => hd y ((interior_subset hy) : y ∈ Set.Ici 0)
  exact h0.trans (hm (by simp) hx hx)

lemma sin_lower_three (x : ℝ) (hx : 0 ≤ x) : x-x^3/6 ≤ Real.sin x := by
  have h := primitive_nonneg (fun x => Real.sin x-x+x^3/6)
    (fun x => Real.cos x-1+x^2/2)
    (by intro y; convert (((Real.hasDerivAt_sin y).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 3).div_const 6)) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; nlinarith [Real.one_sub_sq_div_two_le_cos (x := y)]) x hx
  linarith

lemma cos_upper_four (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1-x^2/2+x^4/24 := by
  have h := primitive_nonneg (fun x => 1-x^2/2+x^4/24-Real.cos x)
    (fun x => Real.sin x-x+x^3/6)
    (by intro y; convert (((hasDerivAt_const y (1:ℝ)).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 4).div_const 24)).sub (Real.hasDerivAt_cos y) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; linarith [sin_lower_three y hy]) x hx
  linarith

lemma sin_upper_five (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x-x^3/6+x^5/120 := by
  have h := primitive_nonneg (fun x => x-x^3/6+x^5/120-Real.sin x)
    (fun x => 1-x^2/2+x^4/24-Real.cos x)
    (by intro y; convert (((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).div_const 6)).add
      (((hasDerivAt_id y).pow 5).div_const 120)).sub (Real.hasDerivAt_sin y) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; linarith [cos_upper_four y hy]) x hx
  linarith

lemma cos_lower_six_nonneg (x : ℝ) (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  have h := primitive_nonneg (fun x => Real.cos x-1+x^2/2-x^4/24+x^6/720)
    (fun x => x-x^3/6+x^5/120-Real.sin x)
    (by intro y; convert ((((Real.hasDerivAt_cos y).sub (hasDerivAt_const y (1:ℝ))).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      (((hasDerivAt_id y).pow 4).div_const 24)).add (((hasDerivAt_id y).pow 6).div_const 720) using 1 ; dsimp ; ring)
    (by simp) (by intro y hy; linarith [sin_upper_five y hy]) x hx
  linarith

lemma cos_lower_six (x : ℝ) : 1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  by_cases hx : 0 ≤ x
  · exact cos_lower_six_nonneg x hx
  · simpa only [neg_sq, Even.neg_pow (by decide : Even 4), Even.neg_pow (by decide : Even 6), Real.cos_neg] using cos_lower_six_nonneg (-x) (by linarith)
end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
open scoped BigOperators
noncomputable section

lemma power_sum_0 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^0 = (N:ℝ) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_1 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^1 = (N:ℝ)*((N:ℝ)-1)/2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_2 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^2 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_3 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^3 = (N:ℝ)^2*((N:ℝ)-1)^2/4 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_4 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^4 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_5 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^5 = (N:ℝ)^2*((N:ℝ)-1)^2*(2*(N:ℝ)^2-2*(N:ℝ)-1)/12 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma power_sum_6 (N : ℕ) : ∑ x ∈ Finset.range N, (x:ℝ)^6 = (N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^4-6*(N:ℝ)^3+3*(N:ℝ)+1)/42 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_poly_six (N : ℕ) (a0 : ℝ) (a1 : ℝ) (a2 : ℝ) (a3 : ℝ) (a4 : ℝ) (a5 : ℝ) (a6 : ℝ) :
    ∑ x ∈ Finset.range N, ((a6)*(x:ℝ)^6 + (a5)*(x:ℝ)^5 + (a4)*(x:ℝ)^4 + (a3)*(x:ℝ)^3 + (a2)*(x:ℝ)^2 + (a1)*(x:ℝ)^1 + (a0)) =
      a6*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^4-6*(N:ℝ)^3+3*(N:ℝ)+1)/42) + a5*((N:ℝ)^2*((N:ℝ)-1)^2*(2*(N:ℝ)^2-2*(N:ℝ)-1)/12) + a4*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30) + a3*((N:ℝ)^2*((N:ℝ)-1)^2/4) + a2*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6) + a1*((N:ℝ)*((N:ℝ)-1)/2) + a0*((N:ℝ)) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, power_sum_1, power_sum_2, power_sum_3, power_sum_4, power_sum_5, power_sum_6,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

lemma difference_sum_4 (N : ℕ) :
    ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^4 = (N:ℝ)^2*((N:ℝ)^2-1)*(2*(N:ℝ)^2-3)/30 := by
  have hi (x : ℕ) : (∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^4) = (0)*(x:ℝ)^6 + (0)*(x:ℝ)^5 + (1*((N:ℝ)))*(x:ℝ)^4 + (-4*((N:ℝ)*((N:ℝ)-1)/2))*(x:ℝ)^3 + (6*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6))*(x:ℝ)^2 + (-4*((N:ℝ)^2*((N:ℝ)-1)^2/4))*(x:ℝ)^1 + (1*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30)) := by
    calc
      _ = ∑ y ∈ Finset.range N, ((0)*(y:ℝ)^6 + (0)*(y:ℝ)^5 + (1*(x:ℝ)^0)*(y:ℝ)^4 + (-4*(x:ℝ)^1)*(y:ℝ)^3 + (6*(x:ℝ)^2)*(y:ℝ)^2 + (-4*(x:ℝ)^3)*(y:ℝ)^1 + (1*(x:ℝ)^4)) := by
        apply Finset.sum_congr rfl; intros; ring
      _ = _ := by rw [sum_poly_six]; ring
  simp_rw [hi]
  rw [sum_poly_six]
  ring

lemma difference_sum_6 (N : ℕ) :
    ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^6 = (N:ℝ)^2*((N:ℝ)^2-1)*(3*(N:ℝ)^4-11*(N:ℝ)^2+10)/84 := by
  have hi (x : ℕ) : (∑ y ∈ Finset.range N, ((x:ℝ)-(y:ℝ))^6) = (1*((N:ℝ)))*(x:ℝ)^6 + (-6*((N:ℝ)*((N:ℝ)-1)/2))*(x:ℝ)^5 + (15*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)/6))*(x:ℝ)^4 + (-20*((N:ℝ)^2*((N:ℝ)-1)^2/4))*(x:ℝ)^3 + (15*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^2-3*(N:ℝ)-1)/30))*(x:ℝ)^2 + (-6*((N:ℝ)^2*((N:ℝ)-1)^2*(2*(N:ℝ)^2-2*(N:ℝ)-1)/12))*(x:ℝ)^1 + (1*((N:ℝ)*((N:ℝ)-1)*(2*(N:ℝ)-1)*(3*(N:ℝ)^4-6*(N:ℝ)^3+3*(N:ℝ)+1)/42)) := by
    calc
      _ = ∑ y ∈ Finset.range N, ((1*(x:ℝ)^0)*(y:ℝ)^6 + (-6*(x:ℝ)^1)*(y:ℝ)^5 + (15*(x:ℝ)^2)*(y:ℝ)^4 + (-20*(x:ℝ)^3)*(y:ℝ)^3 + (15*(x:ℝ)^4)*(y:ℝ)^2 + (-6*(x:ℝ)^5)*(y:ℝ)^1 + (1*(x:ℝ)^6)) := by
        apply Finset.sum_congr rfl; intros; ring
      _ = _ := by rw [sum_poly_six]; ring
  simp_rw [hi]
  rw [sum_poly_six]
  ring

lemma centered_4 (r : ℕ) (hodd : r%2=1) :
    ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^4 = (r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^2-7)/240 := by
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^4) r]
  trans ∑ x ∈ Finset.range r, ((0)*(x:ℝ)^6 + (0)*(x:ℝ)^5 + (1*(-(r/2:ℕ):ℝ)^0)*(x:ℝ)^4 + (4*(-(r/2:ℕ):ℝ)^1)*(x:ℝ)^3 + (6*(-(r/2:ℕ):ℝ)^2)*(x:ℝ)^2 + (4*(-(r/2:ℕ):ℝ)^3)*(x:ℝ)^1 + (1*(-(r/2:ℕ):ℝ)^4))
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_poly_six]
    have he : (r:ℝ) = 2*(r/2:ℕ)+1 := by
      exact_mod_cast (by omega : r = 2*(r/2)+1)
    rw [he]
    ring

lemma centered_6 (r : ℕ) (hodd : r%2=1) :
    ∑ k : Fin r, ((k.val:ℝ)-(r/2:ℕ))^6 = (r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^4-18*(r:ℝ)^2+31)/1344 := by
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => ((x:ℝ)-(r/2:ℕ))^6) r]
  trans ∑ x ∈ Finset.range r, ((1*(-(r/2:ℕ):ℝ)^0)*(x:ℝ)^6 + (6*(-(r/2:ℕ):ℝ)^1)*(x:ℝ)^5 + (15*(-(r/2:ℕ):ℝ)^2)*(x:ℝ)^4 + (20*(-(r/2:ℕ):ℝ)^3)*(x:ℝ)^3 + (15*(-(r/2:ℕ):ℝ)^4)*(x:ℝ)^2 + (6*(-(r/2:ℕ):ℝ)^5)*(x:ℝ)^1 + (1*(-(r/2:ℕ):ℝ)^6))
  · apply Finset.sum_congr rfl; intros; ring
  · rw [sum_poly_six]
    have he : (r:ℝ) = 2*(r/2:ℕ)+1 := by
      exact_mod_cast (by omega : r = 2*(r/2)+1)
    rw [he]
    ring

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

namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Quantum.PhaseEstimation
open scoped BigOperators
noncomputable section

def peakPolynomial (x : ℝ) : ℝ :=
  1-Real.pi^2*x^2/3+2*Real.pi^4*x^4/45-Real.pi^6*x^6/315

def marginalBound : ℝ := 1-Real.pi^2/36+Real.pi^4/1800-Real.pi^6/141120

lemma pi_sq_le_ten : Real.pi^2 ≤ 10 := by
  have h := Real.pi_lt_d6
  nlinarith [Real.pi_pos]

/-- A finite-size proof: expand the squared amplitude, and lower-bound each cosine.
    The finite-size correction is nonnegative, so no limiting argument is needed. -/
lemma geometric_sextic (N : ℕ) (hN : 0<N) (t : ℝ) (ht : |(N:ℝ)*t| ≤ 1/2) :
    peakPolynomial ((N:ℝ)*t) ≤
      Complex.normSq (((N:ℂ)⁻¹) * ∑ x ∈ Finset.range N, eigenvalue t ^ x) := by
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  rw [geometric_normSq]
  have hb := Finset.sum_le_sum (s := Finset.range N) (fun x hx =>
    Finset.sum_le_sum (s := Finset.range N) (fun y hy =>
      cos_lower_six (2*Real.pi*t*((x:ℝ)-(y:ℝ)))))
  have hid : (∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
      (1-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2+
        (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^4/24-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^6/720)) =
      (N:ℝ)^2 - (2*Real.pi^2*t^2)*((N:ℝ)^2*((N:ℝ)^2-1)/6) +
      (2*Real.pi^4*t^4/3)*((N:ℝ)^2*((N:ℝ)^2-1)*(2*(N:ℝ)^2-3)/30) -
      (4*Real.pi^6*t^6/45)*((N:ℝ)^2*((N:ℝ)^2-1)*(3*(N:ℝ)^4-11*(N:ℝ)^2+10)/84) := by
    simp only [show ∀ x y : ℕ,
      (1-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^2/2+
        (2*Real.pi*t*((x:ℝ)-(y:ℝ)))^4/24-(2*Real.pi*t*((x:ℝ)-(y:ℝ)))^6/720) =
      1-(2*Real.pi^2*t^2)*((x:ℝ)-(y:ℝ))^2+
        (2*Real.pi^4*t^4/3)*((x:ℝ)-(y:ℝ))^4-
        (4*Real.pi^6*t^6/45)*((x:ℝ)-(y:ℝ))^6 by intros; ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_range_difference_sq, difference_sum_4, difference_sum_6]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  rw [hid] at hb
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg (N:ℝ)⁻¹)
  let z := Real.pi^2*((N:ℝ)*t)^2
  let w := (N:ℝ)⁻¹^2
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hw0 : 0 ≤ w := sq_nonneg _
  have hz3 : z ≤ 3 := by
    have hx2 : ((N:ℝ)*t)^2 ≤ 1/4 := by nlinarith [sq_abs ((N:ℝ)*t), abs_nonneg ((N:ℝ)*t)]
    calc
      z ≤ 10*((N:ℝ)*t)^2 := mul_le_mul_of_nonneg_right pi_sq_le_ten (sq_nonneg _)
      _ ≤ 3 := by linarith
  have he : (N:ℝ)⁻¹^2 * ((N:ℝ)^2 - (2*Real.pi^2*t^2)*((N:ℝ)^2*((N:ℝ)^2-1)/6) +
      (2*Real.pi^4*t^4/3)*((N:ℝ)^2*((N:ℝ)^2-1)*(2*(N:ℝ)^2-3)/30) -
      (4*Real.pi^6*t^6/45)*((N:ℝ)^2*((N:ℝ)^2-1)*(3*(N:ℝ)^4-11*(N:ℝ)^2+10)/84)) =
      peakPolynomial ((N:ℝ)*t) + w*z*((3-z)/9+w*z*(3-z)/45+(14+10*w^2)*z^2/945) := by
    dsimp [w,z,peakPolynomial]
    field_simp
    ; ring
  rw [he] at hb'
  have hzpos : 0 ≤ 3-z := sub_nonneg.mpr hz3
  have hc : 0 ≤ w*z*((3-z)/9+w*z*(3-z)/45+(14+10*w^2)*z^2/945) := by
    apply mul_nonneg (mul_nonneg hw0 hz0)
    positivity
  linarith

lemma polynomial_marginal (r : ℕ) (hr : 0<r) (hodd : r%2=1) :
    (r:ℝ)*marginalBound ≤ ∑ k : Fin r,
      peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)) := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have he : (∑ k : Fin r, peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ))) =
      (r:ℝ) - (Real.pi^2/(3*(r:ℝ)^2))*((r:ℝ)*((r:ℝ)^2-1)/12) +
      (2*Real.pi^4/(45*(r:ℝ)^4))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^2-7)/240) -
      (Real.pi^6/(315*(r:ℝ)^6))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^4-18*(r:ℝ)^2+31)/1344) := by
    simp only [show ∀ k : Fin r, peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)) =
      1-(Real.pi^2/(3*(r:ℝ)^2))*((k.val:ℝ)-(r/2:ℕ))^2+
      (2*Real.pi^4/(45*(r:ℝ)^4))*((k.val:ℝ)-(r/2:ℕ))^4-
      (Real.pi^6/(315*(r:ℝ)^6))*((k.val:ℝ)-(r/2:ℕ))^6 by intro; dsimp [peakPolynomial]; ring,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      centered_second r hodd, centered_4 r hodd, centered_6 r hodd]
    simp
  rw [he]
  let w := (r:ℝ)⁻¹^2
  have hid : (r:ℝ) - (Real.pi^2/(3*(r:ℝ)^2))*((r:ℝ)*((r:ℝ)^2-1)/12) +
      (2*Real.pi^4/(45*(r:ℝ)^4))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^2-7)/240) -
      (Real.pi^6/(315*(r:ℝ)^6))*((r:ℝ)*((r:ℝ)^2-1)*(3*(r:ℝ)^4-18*(r:ℝ)^2+31)/1344) =
      (r:ℝ)*marginalBound +
      (r:ℝ)*w*Real.pi^2*(15-Real.pi^2)/540 + (r:ℝ)*w*Real.pi^6/20160 +
      (r:ℝ)*w^2*7*Real.pi^4*(56-5*Real.pi^2)/302400 +
      31*(r:ℝ)*Real.pi^6*w^3/423360 := by
    dsimp [w,marginalBound]
    field_simp
    ; ring
  rw [hid]
  have h15 : 0 ≤ 15-Real.pi^2 := by linarith [pi_sq_le_ten]
  have h56 : 0 ≤ 56-5*Real.pi^2 := by linarith [pi_sq_le_ten]
  have hw : 0 ≤ w := sq_nonneg _
  have hc : 0 ≤
      (r:ℝ)*w*Real.pi^2*(15-Real.pi^2)/540 + (r:ℝ)*w*Real.pi^6/20160 +
      (r:ℝ)*w^2*7*Real.pi^4*(56-5*Real.pi^2)/302400 +
      31*(r:ℝ)*Real.pi^6*w^3/423360 := by positivity
  linarith

lemma marginal_numeric : (7731:ℝ)/10000 ≤ marginalBound := by
  have hl : (31415:ℝ)/10000 ≤ Real.pi := by linarith [Real.pi_gt_d6]
  have hu : Real.pi ≤ (31416:ℝ)/10000 := by linarith [Real.pi_lt_d6]
  have h2 := pow_le_pow_left₀ Real.pi_pos.le hu 2
  have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 31415/10000) hl 4
  have h6 := pow_le_pow_left₀ Real.pi_pos.le hu 6
  dsimp [marginalBound]
  norm_num at h2 h4 h6
  linarith

lemma average_peak_sextic (r n : ℕ) [Fact (Nat.Prime r)]
    (hodd : r%2=1) (hNz : ((2^n:ℕ):ZMod r) ≠ 0) :
    (r:ℝ)*marginalBound ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
  have hr := (Fact.out : Nat.Prime r).pos
  have hNR : ((2^n:ℕ):ℝ) ≠ 0 := by positivity
  have h (k : Fin r) : peakPolynomial
      ((((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))/(r:ℝ)) ≤
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val) := by
    have he : ((2^n:ℕ):ℝ)*((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ)) =
        (2^n:ℕ)*(k.val:ℝ)/r - (reducedPeakRaw r n k:ℝ) := by field_simp
    have hs := nearNumerator_abs r n k.val (reducedPeakRaw r n k) hr (reducedPeakRaw_near r n k)
    have hsmall : |((2^n:ℕ):ℝ)*((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ))| ≤ 1/2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ)<(2^n:ℕ))]
      calc
        _ ≤ ((2^n:ℕ):ℝ)*(1/(2*(2^n:ℕ))) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 1/2 := by field_simp
    have hb := geometric_sextic (2^n) (by positivity)
      ((k.val:ℝ)/r-(reducedPeakRaw r n k:ℝ)/(2^n:ℕ)) hsmall
    change _ ≤ Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeakRaw r n k)) at hb
    rw [he, raw_residual r n k hodd, raw_reduced_mass_eq r n k] at hb
    exact hb
  calc
    _ ≤ ∑ k : Fin r, peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)) := polynomial_marginal r hr hodd
    _ = ∑ k : Fin r, peakPolynomial
        ((((residualIndex r (2^n) k).val:ℝ)-(r/2:ℕ))/(r:ℝ)) := by
      exact ((residualIndex_bijective r (2^n) hNz).sum_comp
        (fun k => peakPolynomial (((k.val:ℝ)-(r/2:ℕ))/(r:ℝ)))).symm
    _ ≤ _ := Finset.sum_le_sum (fun k hk => h k)

theorem coverage_of_average (r n m d : ℕ) [Fact (Nat.Prime r)]
    (hn : r < 2^n) (a : ℝ)
    (hl : (r:ℝ)*a ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude n ((k.val:ℝ)/r) (reducedPeak r n k).val))
    (hright : (r:ℝ)*a ≤ ∑ k : Fin r,
      Complex.normSq (paperPhaseAmplitude m ((k.val:ℝ)/r) (reducedPeak r m k).val))
    (hd : (d:ZMod r) ≠ 0) :
    2*a-1-1/(r:ℝ) ≤ reducedCoverageMass r n m d := by
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
  have huSum : (r:ℝ)*a ≤ ∑ k, u k := by
    simpa [u, paper_reduced_eq] using hl
  have hvSum : (r:ℝ)*a ≤ ∑ k, v k := by
    have heq := (characterProduct_bijective r d hd).sum_comp
      (fun k => Complex.normSq (paperPhaseAmplitude m ((k.val:ℝ)/r) (reducedPeak r m k).val))
    dsimp [v]
    rw [heq]
    exact hright
  have hl : (r:ℝ)*(2*a-1)-1 ≤ ∑ k ∈ Finset.univ.erase z, u k*v k := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at he hsum
    linarith
  have hb := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 1/(r:ℝ))
  have hi : (1/(r:ℝ))*((r:ℝ)*(2*a-1)-1) = 2*a-1-1/(r:ℝ) := by
    field_simp
  rw [hi] at hb
  exact hb.trans (coverage_exact_peak_lower r n m d hn)


/-- Our uniform acceptance improvement, valid for every nonzero logarithm. -/
theorem secpCoverage_546 (d : ℕ) (hd : (d:ZMod ShorECDLP.order) ≠ 0) :
    (546:ℝ)/1000 ≤ reducedCoverageMass ShorECDLP.order 256 208 d := by
  letI : Fact (Nat.Prime ShorECDLP.order) := ⟨ShorECDLP.Secp256k1.order_prime⟩
  have htwo : (2:ZMod ShorECDLP.order) ≠ 0 := by
    change ((2:ℕ):ZMod ShorECDLP.order) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff 2 ShorECDLP.order]
    norm_num [ShorECDLP.order]
  have hN : ((2^256:ℕ):ZMod ShorECDLP.order) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ htwo
  have hM : ((2^208:ℕ):ZMod ShorECDLP.order) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ htwo
  have hodd : ShorECDLP.order%2=1 := by norm_num [ShorECDLP.order]
  have hb := coverage_of_average ShorECDLP.order 256 208 d reducedLeftPrecision_order marginalBound
    (average_peak_sextic ShorECDLP.order 256 hodd hN)
    (average_peak_sextic ShorECDLP.order 208 hodd hM) hd
  have hr : 1/(ShorECDLP.order:ℝ) ≤ 1/10000 := by norm_num [ShorECDLP.order]
  have hn : (546:ℝ)/1000 ≤ 2*marginalBound-1-1/(ShorECDLP.order:ℝ) := by
    linarith [marginal_numeric]
  exact hn.trans hb

end
end ShorECDLP.Acceptance

namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Secp256k1
noncomputable section

lemma secpVerified_546 (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    (546:ℝ)/1000 ≤ reducedVerifiedMass Q d := by
  rw [reducedVerifiedMass_eq Q d hd]
  apply secpCoverage_546 d
  intro hz
  have he := (secpCandidate_correct Q d hd (0:ZMod ShorECDLP.order)).mpr hz.symm
  simp only [ZMod.val_zero, zero_nsmul] at he
  exact hn he.symm

end
end ShorECDLP.Acceptance