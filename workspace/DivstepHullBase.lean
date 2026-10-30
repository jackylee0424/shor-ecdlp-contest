import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Int.Parity

/-!
Kernel-small proof obligations for the generated 10-vertex rational polygon.
The five absolute linear forms are the five centrally symmetric facet pairs
emitted by `workspace/divstep_hull.py`.
-/

namespace ShorECDLP.DivstepHullBase

def l0 (f g : ℚ) : ℚ := (-3575 / 8192) * f + (-2825 / 4096) * g
def l1 (f g : ℚ) : ℚ := (-3337 / 16384) * f - g
def l2 (f g : ℚ) : ℚ := (369 / 512) * f - g
def l3 (f g : ℚ) : ℚ := (230625 / 262144) * f + (-89375 / 131072) * g
def l4 (f g : ℚ) : ℚ := (493025 / 524288) * f + (-83425 / 262144) * g

def baseGauge (f g : ℚ) : ℚ :=
  max |l0 f g| (max |l1 f g| (max |l2 f g| (max |l3 f g| |l4 f g|)))

theorem abs_l0_le (f g : ℚ) : |l0 f g| ≤ baseGauge f g := by
  exact le_max_left _ _

theorem abs_l1_le (f g : ℚ) : |l1 f g| ≤ baseGauge f g := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem abs_l2_le (f g : ℚ) : |l2 f g| ≤ baseGauge f g := by
  exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem abs_l3_le (f g : ℚ) : |l3 f g| ≤ baseGauge f g := by
  exact (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)

theorem abs_l4_le (f g : ℚ) : |l4 f g| ≤ baseGauge f g := by
  exact ((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _))

theorem baseGauge_nonneg (f g : ℚ) : 0 ≤ baseGauge f g :=
  (abs_nonneg _).trans (abs_l0_le f g)

theorem abs_g_le_baseGauge (f g : ℚ) : |g| ≤ baseGauge f g := by
  rcases abs_le.mp (abs_l1_le f g) with ⟨h1n, h1p⟩
  rcases abs_le.mp (abs_l2_le f g) with ⟨h2n, h2p⟩
  dsimp [l1, l2] at h1n h1p h2n h2p
  rw [abs_le]
  constructor <;> linarith

private theorem operator_of_facets {f g f' g' : ℚ}
    (h0n : -baseGauge f g ≤ l0 f' g') (h0p : l0 f' g' ≤ baseGauge f g)
    (h1n : -baseGauge f g ≤ l1 f' g') (h1p : l1 f' g' ≤ baseGauge f g)
    (h2n : -baseGauge f g ≤ l2 f' g') (h2p : l2 f' g' ≤ baseGauge f g)
    (h3n : -baseGauge f g ≤ l3 f' g') (h3p : l3 f' g' ≤ baseGauge f g)
    (h4n : -baseGauge f g ≤ l4 f' g') (h4p : l4 f' g' ≤ baseGauge f g) :
    baseGauge f' g' ≤ baseGauge f g := by
  change max |l0 f' g'| (max |l1 f' g'| (max |l2 f' g'| (max |l3 f' g'| |l4 f' g'|))) ≤ _
  exact max_le (abs_le.mpr ⟨h0n, h0p⟩)
    (max_le (abs_le.mpr ⟨h1n, h1p⟩)
      (max_le (abs_le.mpr ⟨h2n, h2p⟩)
        (max_le (abs_le.mpr ⟨h3n, h3p⟩) (abs_le.mpr ⟨h4n, h4p⟩))))

theorem swap_le (f g : ℚ) :
    baseGauge ((32 / 25) * g) ((-16 / 25) * f + (16 / 25) * g) ≤
      baseGauge f g := by
  apply operator_of_facets <;>
    rcases abs_le.mp (abs_l0_le f g) with ⟨b0n, b0p⟩ <;>
    rcases abs_le.mp (abs_l1_le f g) with ⟨b1n, b1p⟩ <;>
    rcases abs_le.mp (abs_l2_le f g) with ⟨b2n, b2p⟩ <;>
    rcases abs_le.mp (abs_l3_le f g) with ⟨b3n, b3p⟩ <;>
    rcases abs_le.mp (abs_l4_le f g) with ⟨b4n, b4p⟩ <;>
    dsimp [l0, l1, l2, l3, l4] at * <;> linarith

theorem neg1Even_le (f g : ℚ) :
    baseGauge ((16384 / 15625) * g)
        ((-8192 / 15625) * f + (4096 / 15625) * g) ≤ baseGauge f g := by
  apply operator_of_facets <;>
    rcases abs_le.mp (abs_l0_le f g) with ⟨b0n, b0p⟩ <;>
    rcases abs_le.mp (abs_l1_le f g) with ⟨b1n, b1p⟩ <;>
    rcases abs_le.mp (abs_l2_le f g) with ⟨b2n, b2p⟩ <;>
    rcases abs_le.mp (abs_l3_le f g) with ⟨b3n, b3p⟩ <;>
    rcases abs_le.mp (abs_l4_le f g) with ⟨b4n, b4p⟩ <;>
    dsimp [l0, l1, l2, l3, l4] at * <;> linarith

theorem neg1Odd_le (f g : ℚ) :
    baseGauge ((16384 / 15625) * g)
        ((-8192 / 15625) * f + (12288 / 15625) * g) ≤ baseGauge f g := by
  apply operator_of_facets <;>
    rcases abs_le.mp (abs_l0_le f g) with ⟨b0n, b0p⟩ <;>
    rcases abs_le.mp (abs_l1_le f g) with ⟨b1n, b1p⟩ <;>
    rcases abs_le.mp (abs_l2_le f g) with ⟨b2n, b2p⟩ <;>
    rcases abs_le.mp (abs_l3_le f g) with ⟨b3n, b3p⟩ <;>
    rcases abs_le.mp (abs_l4_le f g) with ⟨b4n, b4p⟩ <;>
    dsimp [l0, l1, l2, l3, l4] at * <;> linarith

theorem tailEven_le (f g : ℚ) :
    baseGauge ((512 / 625) * f + (128 / 625) * g) ((512 / 625) * g) ≤
      baseGauge f g := by
  apply operator_of_facets <;>
    rcases abs_le.mp (abs_l0_le f g) with ⟨b0n, b0p⟩ <;>
    rcases abs_le.mp (abs_l1_le f g) with ⟨b1n, b1p⟩ <;>
    rcases abs_le.mp (abs_l2_le f g) with ⟨b2n, b2p⟩ <;>
    rcases abs_le.mp (abs_l3_le f g) with ⟨b3n, b3p⟩ <;>
    rcases abs_le.mp (abs_l4_le f g) with ⟨b4n, b4p⟩ <;>
    dsimp [l0, l1, l2, l3, l4] at * <;> linarith

theorem tailOdd_le (f g : ℚ) :
    baseGauge ((512 / 625) * f + (-128 / 625) * g) ((512 / 625) * g) ≤
      baseGauge f g := by
  apply operator_of_facets <;>
    rcases abs_le.mp (abs_l0_le f g) with ⟨b0n, b0p⟩ <;>
    rcases abs_le.mp (abs_l1_le f g) with ⟨b1n, b1p⟩ <;>
    rcases abs_le.mp (abs_l2_le f g) with ⟨b2n, b2p⟩ <;>
    rcases abs_le.mp (abs_l3_le f g) with ⟨b3n, b3p⟩ <;>
    rcases abs_le.mp (abs_l4_le f g) with ⟨b4n, b4p⟩ <;>
    dsimp [l0, l1, l2, l3, l4] at * <;> linarith

theorem baseGauge_add_le (f₁ g₁ f₂ g₂ : ℚ) :
    baseGauge (f₁ + f₂) (g₁ + g₂) ≤ baseGauge f₁ g₁ + baseGauge f₂ g₂ := by
  change max |l0 _ _| (max |l1 _ _| (max |l2 _ _| (max |l3 _ _| |l4 _ _|))) ≤ _
  apply max_le
  · calc
      |l0 (f₁ + f₂) (g₁ + g₂)| = |l0 f₁ g₁ + l0 f₂ g₂| := by congr 1; simp [l0]; ring
      _ ≤ |l0 f₁ g₁| + |l0 f₂ g₂| := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_l0_le _ _) (abs_l0_le _ _)
  · apply max_le
    · calc
        |l1 (f₁ + f₂) (g₁ + g₂)| = |l1 f₁ g₁ + l1 f₂ g₂| := by congr 1; simp [l1]; ring
        _ ≤ |l1 f₁ g₁| + |l1 f₂ g₂| := abs_add_le _ _
        _ ≤ _ := add_le_add (abs_l1_le _ _) (abs_l1_le _ _)
    · apply max_le
      · calc
          |l2 (f₁ + f₂) (g₁ + g₂)| = |l2 f₁ g₁ + l2 f₂ g₂| := by congr 1; simp [l2]; ring
          _ ≤ |l2 f₁ g₁| + |l2 f₂ g₂| := abs_add_le _ _
          _ ≤ _ := add_le_add (abs_l2_le _ _) (abs_l2_le _ _)
      · apply max_le
        · calc
            |l3 (f₁ + f₂) (g₁ + g₂)| = |l3 f₁ g₁ + l3 f₂ g₂| := by congr 1; simp [l3]; ring
            _ ≤ |l3 f₁ g₁| + |l3 f₂ g₂| := abs_add_le _ _
            _ ≤ _ := add_le_add (abs_l3_le _ _) (abs_l3_le _ _)
        · calc
            |l4 (f₁ + f₂) (g₁ + g₂)| = |l4 f₁ g₁ + l4 f₂ g₂| := by congr 1; simp [l4]; ring
            _ ≤ |l4 f₁ g₁| + |l4 f₂ g₂| := abs_add_le _ _
            _ ≤ _ := add_le_add (abs_l4_le _ _) (abs_l4_le _ _)

theorem baseGauge_smul (c f g : ℚ) :
    baseGauge (c * f) (c * g) = |c| * baseGauge f g := by
  simp only [baseGauge, l0, l1, l2, l3, l4]
  have hc : 0 ≤ |c| := abs_nonneg c
  simp only [show (-3575 / 8192) * (c * f) + (-2825 / 4096) * (c * g) =
      c * ((-3575 / 8192) * f + (-2825 / 4096) * g) by ring,
    show (-3337 / 16384) * (c * f) - c * g = c * ((-3337 / 16384) * f - g) by ring,
    show (369 / 512) * (c * f) - c * g = c * ((369 / 512) * f - g) by ring,
    show (230625 / 262144) * (c * f) + (-89375 / 131072) * (c * g) =
      c * ((230625 / 262144) * f + (-89375 / 131072) * g) by ring,
    show (493025 / 524288) * (c * f) + (-83425 / 262144) * (c * g) =
      c * ((493025 / 524288) * f + (-83425 / 262144) * g) by ring,
    abs_mul]
  rw [mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc,
    mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc]

theorem baseGauge_convex (c f₁ g₁ f₂ g₂ : ℚ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    baseGauge (c * f₁ + (1 - c) * f₂) (c * g₁ + (1 - c) * g₂) ≤
      c * baseGauge f₁ g₁ + (1 - c) * baseGauge f₂ g₂ := by
  calc
    baseGauge (c * f₁ + (1 - c) * f₂) (c * g₁ + (1 - c) * g₂) ≤
        baseGauge (c * f₁) (c * g₁) +
          baseGauge ((1 - c) * f₂) ((1 - c) * g₂) := baseGauge_add_le _ _ _ _
    _ = |c| * baseGauge f₁ g₁ + |1 - c| * baseGauge f₂ g₂ := by
      rw [baseGauge_smul, baseGauge_smul]
    _ = c * baseGauge f₁ g₁ + (1 - c) * baseGauge f₂ g₂ := by
      rw [abs_of_nonneg hc0, abs_of_nonneg (sub_nonneg.mpr hc1)]

theorem tailParam_le (z f g : ℚ) (hz : |z| ≤ 1) :
    baseGauge ((512 / 625) * f + (128 / 625) * z * g) ((512 / 625) * g) ≤
      baseGauge f g := by
  let c : ℚ := (1 + z) / 2
  have hz' := abs_le.mp hz
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hconv := baseGauge_convex c
      ((512 / 625) * f + (128 / 625) * g) ((512 / 625) * g)
      ((512 / 625) * f + (-128 / 625) * g) ((512 / 625) * g) hc0 hc1
  have hp := tailEven_le f g
  have hm := tailOdd_le f g
  have hnonneg := baseGauge_nonneg f g
  dsimp [c] at hconv
  calc
    baseGauge ((512 / 625) * f + (128 / 625) * z * g) ((512 / 625) * g) =
        baseGauge (((1 + z) / 2) * ((512 / 625) * f + (128 / 625) * g) +
          (1 - (1 + z) / 2) * ((512 / 625) * f + (-128 / 625) * g))
          (((1 + z) / 2) * ((512 / 625) * g) +
          (1 - (1 + z) / 2) * ((512 / 625) * g)) := by congr 1 <;> ring
    _ ≤ ((1 + z) / 2) * baseGauge ((512 / 625) * f + (128 / 625) * g)
          ((512 / 625) * g) +
        (1 - (1 + z) / 2) * baseGauge ((512 / 625) * f + (-128 / 625) * g)
          ((512 / 625) * g) := hconv
    _ ≤ baseGauge f g := by
      have hc0' : 0 ≤ (1 + z) / 2 := by linarith
      have hc1' : 0 ≤ 1 - (1 + z) / 2 := by linarith
      nlinarith

end ShorECDLP.DivstepHullBase

namespace ShorECDLP.DivstepHull

open DivstepHullBase

def rate : ℚ := 25 / 32

/-- Gauge for `delta2 = 1 + 2*n`. -/
def posGauge (n : Nat) (f g : ℚ) : ℚ :=
  rate ^ n * baseGauge f ((2 : ℚ) ^ n * g)

/-- Gauge for `delta2 = -1 - 2*n`. -/
def negGauge (n : Nat) (f g : ℚ) : ℚ :=
  rate ^ (n + 2) * baseGauge (f - 2 * g) ((2 : ℚ) ^ (n + 1) * f)

theorem posGauge_nonneg (n : Nat) (f g : ℚ) : 0 ≤ posGauge n f g := by
  exact mul_nonneg (pow_nonneg (by norm_num [rate]) _) (baseGauge_nonneg _ _)

theorem negGauge_nonneg (n : Nat) (f g : ℚ) : 0 ≤ negGauge n f g := by
  exact mul_nonneg (pow_nonneg (by norm_num [rate]) _) (baseGauge_nonneg _ _)

theorem pos_even (n : Nat) (f g : ℚ) :
    posGauge (n + 1) f (g / 2) = rate * posGauge n f g := by
  have harg : (2 : ℚ) ^ (n + 1) * (g / 2) = 2 ^ n * g := by
    rw [pow_succ]
    ring
  simp only [posGauge, pow_succ, harg]
  ring

theorem pos_swap_zero (f g : ℚ) :
    posGauge 0 g ((g - f) / 2) ≤ rate * posGauge 0 f g := by
  have h := swap_le f g
  have hs := baseGauge_smul rate ((32 / 25) * g)
    ((-16 / 25) * f + (16 / 25) * g)
  have hr : 0 ≤ rate := by norm_num [rate]
  rw [abs_of_nonneg hr] at hs
  norm_num [posGauge] at ⊢
  calc
    baseGauge g ((g - f) / 2) =
        baseGauge (rate * ((32 / 25) * g))
          (rate * ((-16 / 25) * f + (16 / 25) * g)) := by
            congr 1 <;> norm_num [rate] <;> ring
    _ = rate * baseGauge ((32 / 25) * g)
          ((-16 / 25) * f + (16 / 25) * g) := hs
    _ ≤ rate * baseGauge f g := mul_le_mul_of_nonneg_left h hr

theorem pos_swap_succ (n : Nat) (f g : ℚ) :
    negGauge n g ((g - f) / 2) = rate * posGauge (n + 1) f g := by
  have harg1 : g - 2 * ((g - f) / 2) = f := by ring
  have harg2 : (2 : ℚ) ^ (n + 1) * g = 2 ^ (n + 1) * g := rfl
  simp only [negGauge, posGauge, harg1, harg2, pow_succ]
  ring

theorem neg_zero_even (f g : ℚ) :
    posGauge 0 f (g / 2) ≤ rate * negGauge 0 f g := by
  let u := f - 2 * g
  let v := 2 * f
  have h := neg1Even_le u v
  have hs := baseGauge_smul (rate ^ 3)
    ((16384 / 15625) * v) ((-8192 / 15625) * u + (4096 / 15625) * v)
  have hp : 0 ≤ rate ^ 3 := pow_nonneg (by norm_num [rate]) _
  rw [abs_of_nonneg hp] at hs
  norm_num [posGauge, negGauge] at ⊢
  calc
    baseGauge f (g / 2) = baseGauge
        (rate ^ 3 * ((16384 / 15625) * v))
        (rate ^ 3 * ((-8192 / 15625) * u + (4096 / 15625) * v)) := by
          dsimp [u, v]
          congr 1 <;> norm_num [rate] <;> ring
    _ = rate ^ 3 * baseGauge ((16384 / 15625) * v)
        ((-8192 / 15625) * u + (4096 / 15625) * v) := hs
    _ ≤ rate ^ 3 * baseGauge u v := mul_le_mul_of_nonneg_left h hp
    _ = rate * (rate ^ 2 * baseGauge (f - 2 * g) (2 * f)) := by
      dsimp [u, v]
      ring

theorem neg_zero_odd (f g : ℚ) :
    posGauge 0 f ((g + f) / 2) ≤ rate * negGauge 0 f g := by
  let u := f - 2 * g
  let v := 2 * f
  have h := neg1Odd_le u v
  have hs := baseGauge_smul (rate ^ 3)
    ((16384 / 15625) * v) ((-8192 / 15625) * u + (12288 / 15625) * v)
  have hp : 0 ≤ rate ^ 3 := pow_nonneg (by norm_num [rate]) _
  rw [abs_of_nonneg hp] at hs
  norm_num [posGauge, negGauge] at ⊢
  calc
    baseGauge f ((g + f) / 2) = baseGauge
        (rate ^ 3 * ((16384 / 15625) * v))
        (rate ^ 3 * ((-8192 / 15625) * u + (12288 / 15625) * v)) := by
          dsimp [u, v]
          congr 1 <;> norm_num [rate] <;> ring
    _ = rate ^ 3 * baseGauge ((16384 / 15625) * v)
        ((-8192 / 15625) * u + (12288 / 15625) * v) := hs
    _ ≤ rate ^ 3 * baseGauge u v := mul_le_mul_of_nonneg_left h hp
    _ = rate * (rate ^ 2 * baseGauge (f - 2 * g) (2 * f)) := by
      dsimp [u, v]
      ring

theorem half_pow_abs_le_one (n : Nat) : |((1 / 2 : ℚ) ^ n)| ≤ 1 := by
  rw [abs_of_nonneg (pow_nonneg (by norm_num) _)]
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem neg_succ_even (n : Nat) (f g : ℚ) :
    negGauge n f (g / 2) ≤ rate * negGauge (n + 1) f g := by
  let u := f - 2 * g
  let v := (2 : ℚ) ^ (n + 2) * f
  let z := (1 / 2 : ℚ) ^ n
  have h := tailParam_le z u v (half_pow_abs_le_one n)
  have hs := baseGauge_smul (rate ^ 2)
    ((512 / 625) * u + (128 / 625) * z * v) ((512 / 625) * v)
  have hp : 0 ≤ rate ^ 2 := pow_nonneg (by norm_num [rate]) _
  rw [abs_of_nonneg hp] at hs
  have hpow : (1 / 2 : ℚ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hzv : z * v = 4 * f := by
    dsimp [z, v]
    rw [show (2 : ℚ) ^ (n + 2) = 2 ^ n * 2 ^ 2 by rw [pow_add]]
    calc
      (1 / 2) ^ n * (2 ^ n * 2 ^ 2 * f) = ((1 / 2) ^ n * 2 ^ n) * 2 ^ 2 * f := by ring
      _ = 4 * f := by rw [hpow]; norm_num
  have hcoord1 : rate ^ 2 * ((512 / 625) * u + (128 / 625) * z * v) =
      f - 2 * (g / 2) := by
    dsimp [rate, u]
    rw [show (128 / 625 : ℚ) * z * v = (128 / 625) * (z * v) by ring, hzv]
    norm_num
    ring
  have hcoord2 : rate ^ 2 * ((512 / 625) * v) = (2 : ℚ) ^ (n + 1) * f := by
    dsimp [rate, v]
    rw [show (2 : ℚ) ^ (n + 2) = 2 ^ (n + 1) * 2 by rw [pow_succ]]
    norm_num
    ring
  have hgauge : baseGauge (f - 2 * (g / 2)) ((2 : ℚ) ^ (n + 1) * f) ≤
      rate ^ 2 * baseGauge u v := by
    calc
      baseGauge (f - 2 * (g / 2)) ((2 : ℚ) ^ (n + 1) * f) =
          baseGauge (rate ^ 2 * ((512 / 625) * u + (128 / 625) * z * v))
            (rate ^ 2 * ((512 / 625) * v)) := by rw [hcoord1, hcoord2]
      _ = rate ^ 2 * baseGauge
          ((512 / 625) * u + (128 / 625) * z * v) ((512 / 625) * v) := hs
      _ ≤ rate ^ 2 * baseGauge u v := mul_le_mul_of_nonneg_left h hp
  unfold negGauge
  have hn : 0 ≤ rate ^ (n + 2) := pow_nonneg (by norm_num [rate]) _
  calc
    rate ^ (n + 2) * baseGauge (f - 2 * (g / 2)) (2 ^ (n + 1) * f) ≤
        rate ^ (n + 2) * (rate ^ 2 * baseGauge u v) :=
          mul_le_mul_of_nonneg_left hgauge hn
    _ = rate * (rate ^ (n + 1 + 2) * baseGauge (f - 2 * g) (2 ^ (n + 1 + 1) * f)) := by
      dsimp [u, v]
      rw [show (2 : ℚ) ^ (n + 1 + 1) = 2 ^ (n + 2) by congr 1 <;> omega]
      rw [show rate ^ (n + 2) = rate ^ n * rate ^ 2 by rw [pow_add],
        show rate ^ (n + 1 + 2) = rate ^ n * rate ^ 3 by
          rw [show n + 1 + 2 = n + 3 by omega, pow_add]]
      ring

theorem neg_succ_odd (n : Nat) (f g : ℚ) :
    negGauge n f ((g + f) / 2) ≤ rate * negGauge (n + 1) f g := by
  let u := f - 2 * g
  let v := (2 : ℚ) ^ (n + 2) * f
  let z := -((1 / 2 : ℚ) ^ n)
  have hz : |z| ≤ 1 := by simpa [z] using half_pow_abs_le_one n
  have h := tailParam_le z u v hz
  have hs := baseGauge_smul (rate ^ 2)
    ((512 / 625) * u + (128 / 625) * z * v) ((512 / 625) * v)
  have hp : 0 ≤ rate ^ 2 := pow_nonneg (by norm_num [rate]) _
  rw [abs_of_nonneg hp] at hs
  have hpow : (1 / 2 : ℚ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hzv : z * v = -4 * f := by
    dsimp [z, v]
    rw [show (2 : ℚ) ^ (n + 2) = 2 ^ n * 2 ^ 2 by rw [pow_add]]
    calc
      -(1 / 2) ^ n * (2 ^ n * 2 ^ 2 * f) = -(((1 / 2) ^ n * 2 ^ n) * 2 ^ 2 * f) := by ring
      _ = -4 * f := by rw [hpow]; norm_num
  have hcoord1 : rate ^ 2 * ((512 / 625) * u + (128 / 625) * z * v) =
      f - 2 * ((g + f) / 2) := by
    dsimp [rate, u]
    rw [show (128 / 625 : ℚ) * z * v = (128 / 625) * (z * v) by ring, hzv]
    norm_num
    ring
  have hcoord2 : rate ^ 2 * ((512 / 625) * v) = (2 : ℚ) ^ (n + 1) * f := by
    dsimp [rate, v]
    rw [show (2 : ℚ) ^ (n + 2) = 2 ^ (n + 1) * 2 by rw [pow_succ]]
    norm_num
    ring
  have hgauge : baseGauge (f - 2 * ((g + f) / 2)) ((2 : ℚ) ^ (n + 1) * f) ≤
      rate ^ 2 * baseGauge u v := by
    calc
      baseGauge (f - 2 * ((g + f) / 2)) ((2 : ℚ) ^ (n + 1) * f) =
          baseGauge (rate ^ 2 * ((512 / 625) * u + (128 / 625) * z * v))
            (rate ^ 2 * ((512 / 625) * v)) := by rw [hcoord1, hcoord2]
      _ = rate ^ 2 * baseGauge
          ((512 / 625) * u + (128 / 625) * z * v) ((512 / 625) * v) := hs
      _ ≤ rate ^ 2 * baseGauge u v := mul_le_mul_of_nonneg_left h hp
  unfold negGauge
  have hn : 0 ≤ rate ^ (n + 2) := pow_nonneg (by norm_num [rate]) _
  calc
    rate ^ (n + 2) * baseGauge (f - 2 * ((g + f) / 2)) (2 ^ (n + 1) * f) ≤
        rate ^ (n + 2) * (rate ^ 2 * baseGauge u v) :=
          mul_le_mul_of_nonneg_left hgauge hn
    _ = rate * (rate ^ (n + 1 + 2) * baseGauge (f - 2 * g) (2 ^ (n + 1 + 1) * f)) := by
      dsimp [u, v]
      rw [show (2 : ℚ) ^ (n + 1 + 1) = 2 ^ (n + 2) by congr 1 <;> omega]
      rw [show rate ^ (n + 2) = rate ^ n * rate ^ 2 by rw [pow_add],
        show rate ^ (n + 1 + 2) = rate ^ n * rate ^ 3 by
          rw [show n + 1 + 2 = n + 3 by omega, pow_add]]
      ring

/-- The rational gauge selected by an odd doubled-delta key.  Even keys are
irrelevant: the concrete walk starts odd and preserves oddness. -/
def gauge (delta2 f g : Int) : ℚ :=
  if 0 < delta2 then
    posGauge ((delta2 - 1) / 2).toNat f g
  else
    negGauge ((-delta2 - 1) / 2).toNat f g

@[simp] theorem gauge_pos (n : Nat) (f g : Int) :
    gauge (1 + 2 * (n : Int)) f g = posGauge n f g := by
  unfold gauge
  split
  · congr 1
    omega
  · omega

@[simp] theorem gauge_neg (n : Nat) (f g : Int) :
    gauge (-(1 + 2 * (n : Int))) f g = negGauge n f g := by
  unfold gauge
  split
  · omega
  · congr 1
    omega

theorem odd_delta_cases {delta2 : Int} (hodd : Odd delta2) :
    (∃ n : Nat, delta2 = 1 + 2 * n) ∨
      (∃ n : Nat, delta2 = -(1 + 2 * n)) := by
  obtain ⟨k, hk⟩ := hodd
  by_cases hk0 : 0 ≤ k
  · left
    refine ⟨k.toNat, ?_⟩
    rw [Int.toNat_of_nonneg hk0]
    omega
  · right
    refine ⟨(-k - 1).toNat, ?_⟩
    have hkn : 0 ≤ -k - 1 := by omega
    rw [Int.toNat_of_nonneg hkn]
    omega

theorem gauge_nonneg {delta2 : Int} (hodd : Odd delta2) (f g : Int) :
    0 ≤ gauge delta2 f g := by
  rcases odd_delta_cases hodd with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · simpa using posGauge_nonneg n (f : ℚ) (g : ℚ)
  · rw [gauge_neg]
    exact negGauge_nonneg n (f : ℚ) (g : ℚ)

theorem cast_ediv_two_of_even {x : Int} (hx : Even x) :
    ((x / 2 : Int) : ℚ) = (x : ℚ) / 2 := by
  have htwo : 2 * (x / 2) = x := Int.two_mul_ediv_two_of_even hx
  apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
  exact_mod_cast (by simpa [mul_comm] using htwo)

structure State where
  delta2 : Int
  f : Int
  g : Int
deriving DecidableEq, Repr

def init (f g : Int) : State := ⟨1, f, g⟩

def step (s : State) : State :=
  if s.g = 0 then s
  else if Even s.g then
    ⟨s.delta2 + 2, s.f, s.g / 2⟩
  else if 0 < s.delta2 then
    ⟨2 - s.delta2, s.g, (s.g - s.f) / 2⟩
  else
    ⟨s.delta2 + 2, s.f, (s.g + s.f) / 2⟩

def walk : Nat → State → State
  | 0, s => s
  | k + 1, s => walk k (step s)

@[simp] theorem walk_zero (s : State) : walk 0 s = s := rfl
@[simp] theorem walk_succ (k : Nat) (s : State) : walk (k + 1) s = walk k (step s) := rfl

theorem step_delta_odd {s : State} (hd : Odd s.delta2) : Odd (step s).delta2 := by
  unfold step
  split
  · exact hd
  · split
    · exact hd.add_even (by norm_num)
    · split
      · obtain ⟨k, hk⟩ := hd
        exact ⟨-k, by rw [hk]; ring⟩
      · exact hd.add_even (by norm_num)

theorem step_f_odd {s : State} (hf : Odd s.f) : Odd (step s).f := by
  unfold step
  split
  · exact hf
  · split
    · exact hf
    · split
      · exact Int.not_even_iff_odd.mp ‹¬ Even s.g›
      · exact hf

theorem gauge_step_contracts {s : State} (hd : Odd s.delta2) (hf : Odd s.f)
    (hg0 : s.g ≠ 0) : gauge (step s).delta2 (step s).f (step s).g ≤
      rate * gauge s.delta2 s.f s.g := by
  rcases s with ⟨delta2, f, g⟩
  simp only [State.delta2, State.f, State.g] at hd hf hg0 ⊢
  rcases odd_delta_cases hd with ⟨n, hn⟩ | ⟨n, hn⟩
  · subst delta2
    unfold step
    simp only [State.g, hg0, ↓reduceIte]
    split
    · rename_i heven
      have hcast := cast_ediv_two_of_even heven
      simp only [State.delta2, State.f, State.g]
      rw [show 1 + 2 * (n : Int) + 2 = 1 + 2 * ((n + 1 : Nat) : Int) by push_cast; ring,
        gauge_pos, gauge_pos, hcast]
      exact le_of_eq (pos_even n (f : ℚ) (g : ℚ))
    · rename_i hneven
      have hgodd : Odd g := Int.not_even_iff_odd.mp hneven
      have hdiff : Even (g - f) := hgodd.sub_odd hf
      have hcast := cast_ediv_two_of_even hdiff
      simp only [show (0 : Int) < 1 + 2 * n by omega, ↓reduceIte,
        State.delta2, State.f, State.g]
      cases n with
      | zero =>
          rw [show 2 - (1 + 2 * (0 : Nat)) = 1 + 2 * ((0 : Nat) : Int) by norm_num,
            gauge_pos, gauge_pos, hcast]
          push_cast
          exact pos_swap_zero (f : ℚ) (g : ℚ)
      | succ n =>
          rw [show 2 - (1 + 2 * ((n + 1 : Nat) : Int)) =
              -(1 + 2 * (n : Int)) by push_cast; ring,
            gauge_neg, gauge_pos, hcast]
          push_cast
          exact le_of_eq (pos_swap_succ n (f : ℚ) (g : ℚ))
  · subst delta2
    unfold step
    simp only [State.g, hg0, ↓reduceIte]
    split
    · rename_i heven
      have hcast := cast_ediv_two_of_even heven
      simp only [State.delta2, State.f, State.g]
      cases n with
      | zero =>
          rw [show -(1 + 2 * (0 : Nat)) + 2 = 1 + 2 * ((0 : Nat) : Int) by norm_num,
            gauge_pos, gauge_neg, hcast]
          exact neg_zero_even (f : ℚ) (g : ℚ)
      | succ n =>
          rw [show -(1 + 2 * ((n + 1 : Nat) : Int)) + 2 =
              -(1 + 2 * (n : Int)) by push_cast; ring,
            gauge_neg, gauge_neg, hcast]
          exact neg_succ_even n (f : ℚ) (g : ℚ)
    · rename_i hneven
      have hgodd : Odd g := Int.not_even_iff_odd.mp hneven
      have hsum : Even (g + f) := hgodd.add_odd hf
      have hcast := cast_ediv_two_of_even hsum
      simp only [show ¬(0 : Int) < -(1 + 2 * n) by omega, ↓reduceIte,
        State.delta2, State.f, State.g]
      cases n with
      | zero =>
          rw [show -(1 + 2 * (0 : Nat)) + 2 = 1 + 2 * ((0 : Nat) : Int) by norm_num,
            gauge_pos, gauge_neg, hcast]
          push_cast
          exact neg_zero_odd (f : ℚ) (g : ℚ)
      | succ n =>
          rw [show -(1 + 2 * ((n + 1 : Nat) : Int)) + 2 =
              -(1 + 2 * (n : Int)) by push_cast; ring,
            gauge_neg, gauge_neg, hcast]
          push_cast
          exact neg_succ_odd n (f : ℚ) (g : ℚ)

theorem step_of_g_zero {s : State} (hg : s.g = 0) : step s = s := by
  simp [step, hg]

theorem walk_of_g_zero {s : State} (hg : s.g = 0) (k : Nat) : walk k s = s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp [walk, step_of_g_zero hg, ih hg]

theorem start_g_ne_zero_of_walk_g_ne_zero {s : State} {k : Nat}
    (h : (walk k s).g ≠ 0) : s.g ≠ 0 := by
  intro hs
  rw [walk_of_g_zero hs k] at h
  exact h hs

theorem walk_delta_odd {s : State} (hd : Odd s.delta2) (k : Nat) :
    Odd (walk k s).delta2 := by
  induction k generalizing s with
  | zero => exact hd
  | succ k ih => exact ih (step_delta_odd hd)

theorem walk_f_odd {s : State} (hf : Odd s.f) (k : Nat) : Odd (walk k s).f := by
  induction k generalizing s with
  | zero => exact hf
  | succ k ih => exact ih (step_f_odd hf)

theorem walk_succ_last (k : Nat) (s : State) : walk (k + 1) s = step (walk k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simpa [walk] using ih (step s)

theorem gauge_walk_bound {s : State} (hd : Odd s.delta2) (hf : Odd s.f)
    {k : Nat} (hfinal : (walk k s).g ≠ 0) :
    gauge (walk k s).delta2 (walk k s).f (walk k s).g ≤
      rate ^ k * gauge s.delta2 s.f s.g := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      have hstepfinal : (walk k (step s)).g ≠ 0 := hfinal
      have hsg : s.g ≠ 0 := start_g_ne_zero_of_walk_g_ne_zero hfinal
      have hrec := ih (step_delta_odd hd) (step_f_odd hf) hstepfinal
      have hone := gauge_step_contracts hd hf hsg
      have hpow : 0 ≤ rate ^ k := pow_nonneg (by norm_num [rate]) _
      rw [pow_succ]
      exact hrec.trans (by
        calc
          rate ^ k * gauge (step s).delta2 (step s).f (step s).g ≤
              rate ^ k * (rate * gauge s.delta2 s.f s.g) :=
                mul_le_mul_of_nonneg_left hone hpow
          _ = rate ^ k * rate * gauge s.delta2 s.f s.g := by ring)

def rankBase : ℚ := 16 / 25

def rankFactor (delta2 : Int) : ℚ :=
  if 0 < delta2 then rankBase ^ (((delta2 - 1) / 2).toNat)
  else rankBase ^ (((-delta2 - 1) / 2).toNat)

@[simp] theorem rankFactor_pos (n : Nat) :
    rankFactor (1 + 2 * (n : Int)) = rankBase ^ n := by
  unfold rankFactor
  split
  · congr 1
    omega
  · omega

@[simp] theorem rankFactor_neg (n : Nat) :
    rankFactor (-(1 + 2 * (n : Int))) = rankBase ^ n := by
  unfold rankFactor
  split
  · omega
  · congr 1
    omega

theorem rankFactor_nonneg (delta2 : Int) : 0 ≤ rankFactor delta2 := by
  unfold rankFactor
  split <;> exact pow_nonneg (by norm_num [rankBase]) _

theorem rankFactor_le_one {delta2 : Int} (hd : Odd delta2) : rankFactor delta2 ≤ 1 := by
  rcases odd_delta_cases hd with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [rankFactor_pos]
    exact pow_le_one₀ (by norm_num [rankBase]) (by norm_num [rankBase])
  · rw [rankFactor_neg]
    exact pow_le_one₀ (by norm_num [rankBase]) (by norm_num [rankBase])

theorem pos_rank_dominates (n : Nat) (f g : Int) :
    (Int.natAbs g : ℚ) ≤ rankBase ^ n * posGauge n f g := by
  have h := abs_g_le_baseGauge (f : ℚ) ((2 : ℚ) ^ n * g)
  have hc : 0 ≤ rankBase ^ n * rate ^ n :=
    mul_nonneg (pow_nonneg (by norm_num [rankBase]) _)
      (pow_nonneg (by norm_num [rate]) _)
  have hm := mul_le_mul_of_nonneg_left h hc
  have hscale : rankBase ^ n * rate ^ n * (2 : ℚ) ^ n = 1 := by
    rw [← mul_pow, ← mul_pow]
    norm_num [rankBase, rate]
  rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)] at hm
  have habs : (Int.natAbs g : ℚ) = |(g : ℚ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  calc
    (Int.natAbs g : ℚ) = |(g : ℚ)| := habs
    _ = (rankBase ^ n * rate ^ n * 2 ^ n) * |(g : ℚ)| := by rw [hscale]; ring
    _ ≤ rankBase ^ n * rate ^ n * baseGauge (f : ℚ) (2 ^ n * (g : ℚ)) := by
      simpa only [mul_assoc] using hm
    _ = rankBase ^ n * posGauge n f g := by simp [posGauge]; ring

theorem rankFactor_step_of_negative {s : State} (hd : Odd s.delta2)
    (hg0 : s.g ≠ 0) (hneg : (step s).delta2 < 0) :
    rankFactor (step s).delta2 = (2 * rate) * rankFactor s.delta2 := by
  rcases s with ⟨delta2, f, g⟩
  simp only [State.delta2, State.g] at hd hg0 hneg ⊢
  rcases odd_delta_cases hd with ⟨n, hn⟩ | ⟨n, hn⟩
  · subst delta2
    unfold step at hneg ⊢
    rw [if_neg hg0] at hneg ⊢
    simp only [State.g, State.delta2] at hneg ⊢
    split
    · omega
    · simp only [show (0 : Int) < 1 + 2 * n by omega, ↓reduceIte, State.delta2]
      cases n with
      | zero => norm_num at hneg
      | succ n =>
          rw [show 2 - (1 + 2 * ((n + 1 : Nat) : Int)) = -(1 + 2 * (n : Int)) by
              push_cast; ring,
            rankFactor_neg, rankFactor_pos, pow_succ]
          norm_num [rankBase, rate]
          ring
  · subst delta2
    unfold step at hneg ⊢
    rw [if_neg hg0] at hneg ⊢
    simp only [State.g, State.delta2] at hneg ⊢
    split
    · simp only [State.delta2]
      cases n with
      | zero => norm_num at hneg
      | succ n =>
          rw [show -(1 + 2 * ((n + 1 : Nat) : Int)) + 2 = -(1 + 2 * (n : Int)) by
              push_cast; ring,
            rankFactor_neg, rankFactor_neg, pow_succ]
          norm_num [rankBase, rate]
          ring
    · simp only [show ¬(0 : Int) < -(1 + 2 * n) by omega, ↓reduceIte, State.delta2]
      cases n with
      | zero => norm_num at hneg
      | succ n =>
          rw [show -(1 + 2 * ((n + 1 : Nat) : Int)) + 2 = -(1 + 2 * (n : Int)) by
              push_cast; ring,
            rankFactor_neg, rankFactor_neg, pow_succ]
          norm_num [rankBase, rate]
          ring

end ShorECDLP.DivstepHull
