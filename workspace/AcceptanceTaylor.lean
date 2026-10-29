import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedCoverage
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
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
      (((hasDerivAt_id y).pow 3).div_const 6)) using 1 <;> dsimp <;> ring)
    (by simp) (by intro y hy; nlinarith [Real.one_sub_sq_div_two_le_cos (x := y)]) x hx
  linarith

lemma cos_upper_four (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ 1-x^2/2+x^4/24 := by
  have h := primitive_nonneg (fun x => 1-x^2/2+x^4/24-Real.cos x)
    (fun x => Real.sin x-x+x^3/6)
    (by intro y; convert (((hasDerivAt_const y (1:ℝ)).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 4).div_const 24)).sub (Real.hasDerivAt_cos y) using 1 <;> dsimp <;> ring)
    (by simp) (by intro y hy; linarith [sin_lower_three y hy]) x hx
  linarith

lemma sin_upper_five (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ x-x^3/6+x^5/120 := by
  have h := primitive_nonneg (fun x => x-x^3/6+x^5/120-Real.sin x)
    (fun x => 1-x^2/2+x^4/24-Real.cos x)
    (by intro y; convert (((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 3).div_const 6)).add
      (((hasDerivAt_id y).pow 5).div_const 120)).sub (Real.hasDerivAt_sin y) using 1 <;> dsimp <;> ring)
    (by simp) (by intro y hy; linarith [cos_upper_four y hy]) x hx
  linarith

lemma cos_lower_six_nonneg (x : ℝ) (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  have h := primitive_nonneg (fun x => Real.cos x-1+x^2/2-x^4/24+x^6/720)
    (fun x => x-x^3/6+x^5/120-Real.sin x)
    (by intro y; convert ((((Real.hasDerivAt_cos y).sub (hasDerivAt_const y (1:ℝ))).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
      (((hasDerivAt_id y).pow 4).div_const 24)).add (((hasDerivAt_id y).pow 6).div_const 720) using 1 <;> dsimp <;> ring)
    (by simp) (by intro y hy; linarith [sin_upper_five y hy]) x hx
  linarith

lemma cos_lower_six (x : ℝ) : 1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  by_cases hx : 0 ≤ x
  · exact cos_lower_six_nonneg x hx
  · simpa only [neg_sq, Even.neg_pow (by decide : Even 4), Even.neg_pow (by decide : Even 6), Real.cos_neg] using cos_lower_six_nonneg (-x) (by linarith)
end
end ShorECDLP.Acceptance
