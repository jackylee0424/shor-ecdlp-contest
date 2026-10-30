import ShorECDLP.Submission.Entrant.Compiler

/-!
# Canonical signed modular cell algebra for Brief 22

The physical representation is complemented for subtraction.  This makes the
same final `+ q*c` pass correct in both signs, avoiding a nonlinear sign/quotient
product.  All quantities below are ordinary finite-word integers; no exceptional
band is omitted.
-/

namespace ShorECDLP.Entrant.FastMul

open Paper2607_13816

def addReduced (p z y : Nat) : Nat :=
  if p <= z + y then z + y - p else z + y

def subReduced (p z y : Nat) : Nat :=
  if z < y then z + p - y else z - y

def wordAdd (radix x y : Nat) : Nat :=
  if radix <= x + y then x + y - radix else x + y

def signedRaw (radix z y : Nat) (positive : Bool) : Nat :=
  if positive then wordAdd radix z y
  else if z < y then y - z - 1 else radix - 1 - (z - y)

def signedQuotient (p radix z y : Nat) (positive : Bool) : Bool :=
  if positive then decide (radix <= z + y) || decide (p <= wordAdd radix z y)
  else decide (z < y)

def correctedTransformed (radix c raw : Nat) (quotient : Bool) : Nat :=
  if quotient then wordAdd radix raw c else raw

def signedPhysicalResult (p radix c z y : Nat) (positive : Bool) : Nat :=
  let corrected := correctedTransformed radix c (signedRaw radix z y positive)
    (signedQuotient p radix z y positive)
  if positive then corrected else radix - 1 - corrected

theorem signedRaw_lt (radix z y : Nat) (positive : Bool)
    (hz : z < radix) (hy : y < radix) :
    signedRaw radix z y positive < radix := by
  cases positive <;> simp only [signedRaw, Bool.false_eq_true, if_false, if_true]
  · split <;> omega
  · unfold wordAdd
    split <;> omega

theorem signedPhysical_eq (p radix c z y : Nat) (positive : Bool)
    (hc : c < radix) (hp : p = radix - c)
    (hz : z < p) (hy : y < p) :
    signedPhysicalResult p radix c z y positive =
      if positive then addReduced p z y else subReduced p z y := by
  subst p
  cases positive
  · simp only [signedPhysicalResult, signedRaw, signedQuotient,
      Bool.false_eq_true, if_false, correctedTransformed]
    by_cases hzy : z < y
    · simp [hzy, subReduced, wordAdd]
      split <;> omega
    · simp [hzy, subReduced]
      omega
  · simp only [signedPhysicalResult, signedRaw, signedQuotient,
      if_true, correctedTransformed]
    by_cases hradix : radix <= z + y
    · have hpSum : radix - c <= z + y := by omega
      simp [wordAdd, hradix, addReduced, hpSum]
      split <;> omega
    · by_cases hpSum : radix - c <= z + y
      · simp [wordAdd, hradix, addReduced, hpSum]
        split <;> omega
      · simp [wordAdd, hradix, addReduced, hpSum]

theorem signedPhysical_canonical (p radix c z y : Nat) (positive : Bool)
    (hc : c < radix) (hp : p = radix - c)
    (hz : z < p) (hy : y < p) :
    signedPhysicalResult p radix c z y positive < p := by
  rw [signedPhysical_eq p radix c z y positive hc hp hz hy]
  cases positive <;> simp only [Bool.false_eq_true, if_false, if_true]
  · unfold subReduced
    split <;> omega
  · unfold addReduced
    split <;> omega

theorem secp_signedPhysical_eq (z y : Nat) (positive : Bool)
    (hz : z < ShorECDLP.p) (hy : y < ShorECDLP.p) :
    signedPhysicalResult ShorECDLP.p (2^256) (2^32 + 977) z y positive =
      if positive then addReduced ShorECDLP.p z y
      else subReduced ShorECDLP.p z y := by
  apply signedPhysical_eq <;> norm_num [ShorECDLP.p] <;> assumption

end ShorECDLP.Entrant.FastMul
