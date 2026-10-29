import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace

/-!
# Exact algebraic core for Brief 16

These lemmas isolate the pseudo-Mersenne and signed-digit identities from the
physical carry implementation.  No probabilistic truncation is present.
-/

namespace ShorECDLP.Paper2607_13816.FastMul

def foldC : Nat := 2 ^ 32 + 977

theorem secp256k1_eq : ShorECDLP.p = 2 ^ 256 - foldC := by
  rfl

theorem foldC_lt_pow : foldC < 2 ^ 256 := by
  norm_num [foldC]

theorem pow256_mod_p : 2 ^ 256 % ShorECDLP.p = foldC := by
  have hsplit : 2 ^ 256 = ShorECDLP.p + foldC := by
    rw [secp256k1_eq]
    exact (Nat.sub_add_cancel (Nat.le_of_lt foldC_lt_pow)).symm
  have hsmall : foldC < ShorECDLP.p := by
    rw [secp256k1_eq]
    norm_num [foldC]
  rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt hsmall]

theorem pow256_modEq : Nat.ModEq ShorECDLP.p (2 ^ 256) foldC := by
  exact pow256_mod_p

/-- Replacing one raw `2^256` carry by `c=2^32+977` is exact modulo p. -/
theorem fold_raw_carry (lo k : Nat) :
    Nat.ModEq ShorECDLP.p (lo + k * 2 ^ 256) (lo + k * foldC) := by
  exact (Nat.ModEq.refl lo).add (pow256_modEq.mul_left k)

/-- The signed-digit used at position `k` is always `-1` or `+1`. -/
def signedDigit (b : Bool) : Int := if b then 1 else -1

theorem signedDigit_eq (b : Bool) : signedDigit b = 2 * b.toNat - 1 := by
  cases b <;> rfl

/-- One Horner step has the intended integer value before modular folding. -/
theorem signed_horner_step (z y : Int) (b : Bool) :
    2 * (z + signedDigit b * y) = 2 * z + (2 * b.toNat - 1) * (2 * y) := by
  rw [signedDigit_eq]
  ring

end ShorECDLP.Paper2607_13816.FastMul
