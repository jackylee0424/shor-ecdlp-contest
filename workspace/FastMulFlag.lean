import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
import ShorECDLP.Framework.Quantum.MeasurementUncompute

/-!
# Exact quotient-flag identities for the conservative fast multiplier

The fast cell considered in Brief 20 canonicalises the signed modular add
before it doubles or halves.  These elementary identities show that the
quotient/borrow flag is recoverable from the corrected output and the
surviving addend.  The final section checks the one-bit measurement erasure
against the benchmark's normalized adaptive semantics.
-/

namespace ShorECDLP.Paper2607_13816.FastMul

open Quantum

/-- Canonical representative of `z+y`, assuming both inputs are below `p`. -/
def addReduced (p z y : Nat) : Nat :=
  if p ≤ z + y then z + y - p else z + y

/-- After an exact modular add, the quotient flag is exactly `result < y`.
This is the full-width predicate that replaces the donor's top-32 comparison. -/
theorem add_quotient_from_output (p z y : Nat)
    (hz : z < p) :
    p ≤ z + y ↔ addReduced p z y < y := by
  unfold addReduced
  split <;> omega

/-- Canonical representative of `z-y`, with a modulus added on borrow. -/
def subReduced (p z y : Nat) : Nat :=
  if z < y then z + p - y else z - y

/-- After an exact modular subtraction, the borrow flag is exactly the
quotient of `result+y` by `p`. -/
theorem sub_borrow_from_output (p z y : Nat)
    (hz : z < p) :
    z < y ↔ p ≤ subReduced p z y + y := by
  unfold subReduced
  split <;> omega

/-- Canonical representative of a modular doubling. -/
def doubleReduced (p z : Nat) : Nat :=
  if p ≤ 2 * z then 2 * z - p else 2 * z

/-- For an odd modulus, the doubling quotient is the corrected result's low
bit.  Thus a coherently held quotient flag can be cleared by one CNOT, rather
than by another comparison. -/
theorem double_quotient_from_output_lsb (p z k : Nat)
    (hp : p = 2 * k + 1) (hz : z < p) :
    p ≤ 2 * z ↔ doubleReduced p z % 2 = 1 := by
  subst p
  unfold doubleReduced
  split
  · rename_i hq
    have hkz : k < z := by omega
    have heq : 2 * z - (2 * k + 1) = 2 * (z - k - 1) + 1 := by omega
    rw [heq]
    omega
  · rename_i hq
    simp only [Nat.mul_mod_right]
    omega

noncomputable section

/-- A cleanable flag that is a copy of a surviving computational-basis bit. -/
def CopiedBit (source flag : Wire) (state : BasisState) : Prop :=
  state flag = state source

/-- The true X-measurement outcome pays the copied bit's phase with Pauli Z. -/
def copiedBitCorrection (source : Wire) : List Bool → Circuit
  | [true] => pauliZ source
  | _ => []

theorem copiedBitCorrection_phase (source flag : Wire)
    (hsf : source ≠ flag) :
    RegisterXPhaseCorrectionOn [flag] (copiedBitCorrection source)
      (CopiedBit source flag) := by
  intro outcomes hlength state hcopy
  cases outcomes with
  | nil => simp at hlength
  | cons outcome outcomes =>
      have houtcomes : outcomes = [] := by simpa using hlength
      subst outcomes
      cases outcome with
      | false =>
          simp [copiedBitCorrection, clearRegister, registerXPhase]
      | true =>
          simp only [copiedBitCorrection]
          rw [run_pauliZ_ket]
          have hsource : clearRegister [flag] state source = state source := by
            simp [clearRegister, upd, hsf]
          rw [hsource, ← hcopy]
          simp [registerXPhase]

/-- Benchmark-semantic check: X-measure/reset plus a selected Clifford Z
coherently clears a copied quotient flag, with no T gate in the correction. -/
theorem eraseCopiedBit_coherent (source flag : Wire)
    (hsf : source ≠ flag) :
    CoherentlyImplementsOn
      (measureResetWithCorrection [flag] (copiedBitCorrection source))
      (clearRegisterMap [flag]) (CopiedBit source flag) := by
  apply measureResetWithCorrection_coherent
  · simp
  · exact copiedBitCorrection_phase source flag hsf

@[simp] theorem copiedBitCorrection_tCount (source : Wire) (outcome : Bool) :
    ShorECDLP.tCount (copiedBitCorrection source (outcome :: [])) = 0 := by
  cases outcome <;> rfl

end

end ShorECDLP.Paper2607_13816.FastMul
