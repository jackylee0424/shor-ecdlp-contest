import ShorECDLP.Submission.«2607_13816».OrderFinding.ReducedCoverage
import Mathlib.Tactic
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
