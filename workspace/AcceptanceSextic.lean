import Mathlib.Analysis.Real.Pi.Bounds
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
