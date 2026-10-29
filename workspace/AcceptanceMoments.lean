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
