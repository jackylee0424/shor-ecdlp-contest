import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Pure
import ShorECDLP.Submission.Entrant.Streaming.Challenge.BatchedWindowState

namespace ShorECDLP.FlagCorrection

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

local instance : Fact (Nat.Prime ShorECDLP.p) := ⟨p_prime⟩

theorem windowPoint_order (Q : Point) (hQ : order • Q = 0) (w : OddWindow) (a : Nat) :
    order • windowPoint Q w a = 0 := by
  cases w with
  | left j =>
      simp only [windowPoint]
      rw [← oddCoefficient_point]
      simp only [smul_smul]
      rw [Nat.mul_comm]
      rw [← smul_smul, generator_nsmul_eq_zero, nsmul_zero]
  | right j =>
      simp only [windowPoint]
      rw [← oddCoefficient_point]
      simp only [smul_smul]
      rw [Nat.mul_comm]
      rw [← smul_smul, hQ, nsmul_zero]

theorem two_three_nsmul_ne_zero (C : Point) (horder : order • C = 0) (hC : C ≠ 0) :
    2 • C ≠ 0 ∧ 3 • C ≠ 0 := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf C = order := addOrderOf_eq_prime horder hC
  constructor
  · intro hz
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    rw [ho] at hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    have hl := order_prime.two_le
    norm_num [order] at this
  · intro hz
    have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    rw [ho] at hd
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    norm_num [order] at this

theorem six_nsmul_ne_zero (C : Point) (horder : order • C = 0) (hC : C ≠ 0) :
    6 • C ≠ 0 := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf C = order := addOrderOf_eq_prime horder hC
  intro hz
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
  rw [ho] at hd
  have := Nat.le_of_dvd (by decide : 0 < 6) hd
  norm_num [order] at this

def exceptionInputAt (C : Point) : Fin 4 → Point
  | 0 => 0
  | 1 => C
  | 2 => -C
  | 3 => -(C + C)

def exceptionNat : Fin 4 → Nat
  | 0 => 0
  | 1 => 1
  | 2 => order - 1
  | 3 => order - 2

theorem exceptionNat_lt (k : Fin 4) : exceptionNat k < order := by
  fin_cases k <;> simp [exceptionNat] <;> norm_num [order]

theorem exceptionInputAt_eq_nsmul (C : Point) (horder : order • C = 0) (k : Fin 4) :
    exceptionInputAt C k = exceptionNat k • C := by
  fin_cases k
  · simp [exceptionInputAt, exceptionNat]
  · simp [exceptionInputAt, exceptionNat]
  · rw [exceptionInputAt.eq_def, exceptionNat.eq_def,
      sub_nsmul C (by norm_num [order] : 1 ≤ order),
      horder, one_nsmul, zero_add]
  · rw [exceptionInputAt.eq_def, exceptionNat.eq_def,
      sub_nsmul C (by norm_num [order] : 2 ≤ order),
      horder, two_nsmul, zero_add]

theorem exceptionInputAt_injective (C : Point) (horder : order • C = 0) (hC : C ≠ 0) :
    Function.Injective (exceptionInputAt C) := by
  letI : Fact (Nat.Prime order) := ⟨order_prime⟩
  have ho : addOrderOf C = order := addOrderOf_eq_prime horder hC
  intro i j hij
  rw [exceptionInputAt_eq_nsmul C horder i, exceptionInputAt_eq_nsmul C horder j,
    nsmul_eq_nsmul_iff_modEq, ho] at hij
  have he := hij.eq_of_lt_of_lt (exceptionNat_lt i) (exceptionNat_lt j)
  fin_cases i <;> fin_cases j <;> try norm_num [exceptionNat.eq_def, order] at he
  all_goals rfl

def endpointSource (x y : Fp) (C : Point) (k : Fin 4) : FlagWord :=
  coordinateWordBits (fig14EncodedEquiv x y (fig14PointEncoding (exceptionInputAt C k)))

def endpointTarget (C : Point) (k : Fin 4) : FlagWord :=
  coordinateWordBits (fig14PointEncoding (exceptionInputAt C k + C))

theorem endpointSource_injective (x y : Fp) (C : Point)
    (hE : Function.Injective (exceptionInputAt C)) :
    Function.Injective (endpointSource x y C) :=
  coordinateWordBits_injective.comp
    ((fig14EncodedEquiv x y).injective.comp (fig14PointEncoding_injective.comp hE))

theorem endpointTarget_injective (C : Point)
    (hE : Function.Injective (exceptionInputAt C)) :
    Function.Injective (endpointTarget C) := by
  intro i j h
  have hp := fig14PointEncoding_injective (coordinateWordBits_injective h)
  exact hE (add_right_cancel hp)

theorem normalizedEndpointWords_eq_model {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (row : Fin n) {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) :
    (fun j => normalizedEndpointWords coeffs Q row j) =
      modelWords (endpointSource x y (.some hC)) (endpointTarget (.some hC)) := by
  funext j
  have hp := readEndpointWords_pairs coeffs Q row
  rw [hrow, protectedExceptionPairs_eq hC] at hp
  simp [fixedExceptionPairs, fixedExceptionInputs] at hp
  rw [normalizedEndpointWords_finite coeffs Q row hC hrow]
  fin_cases j <;> simp [modelWords, endpointSource, endpointTarget, exceptionInputAt]
  all_goals aesop

end ShorECDLP.FlagCorrection
