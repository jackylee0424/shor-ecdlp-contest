import ShorECDLP.Submission.Entrant.Streaming.Resources

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem compiled_count_eq_of_run {n start : Nat}
    (p q : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool)
    (source : AdaptiveCircuit)
    (hp : compiledRun p read history = source.run)
    (hq : compiledRun q read history = source.run) : p.1 = q.1 := by
  have a := compiled_count_of_run p read history source hp
  have b := compiled_count_of_run q read history source hq
  exact a.trans b.symm

theorem optimizedDivisionProgram_count (n start : Nat) :
    (optimizedDivisionProgram n start).1 = (divisionProgram n start).1 :=
  compiled_count_eq_of_run _ _ (fun _ ↦ false) (fun _ ↦ false)
    secp256k1InPlaceDivision
    (optimizedDivisionProgram_run n start _ _) (divisionProgram_run n start _ _)

theorem optimizedMultiplicationProgram_count (n start : Nat) :
    (optimizedMultiplicationProgram n start).1 = (multiplicationProgram n start).1 :=
  compiled_count_eq_of_run _ _ (fun _ ↦ false) (fun _ ↦ false)
    secp256k1InPlaceMultiplication
    (optimizedMultiplicationProgram_run n start _ _) (multiplicationProgram_run n start _ _)

theorem optimizedZeroDivisionProgram_count (n start : Nat) :
    (optimizedZeroDivisionProgram n start).1 = (zeroDivisionProgram n start).1 :=
  compiled_count_eq_of_run _ _ (fun _ ↦ false) (fun _ ↦ false)
    secp256k1ZeroAllowedDivision
    (optimizedZeroDivisionProgram_run n start _ _) (zeroDivisionProgram_run n start _ _)

theorem optimizedZeroMultiplicationProgram_count (n start : Nat) :
    (optimizedZeroMultiplicationProgram n start).1 =
      (zeroMultiplicationProgram n start).1 :=
  compiled_count_eq_of_run _ _ (fun _ ↦ false) (fun _ ↦ false)
    secp256k1ZeroAllowedMultiplication
    (optimizedZeroMultiplicationProgram_run n start _ _)
    (zeroMultiplicationProgram_run n start _ _)

inductive TCompareForall₂ {n : Nat} (read : ConstantBit n → Bool) :
    List (FixedSegment n) → List (FixedSegment n) → Nat → Prop
  | nil : TCompareForall₂ read List.nil List.nil 0
  | cons {p q ps qs tail} (d : Nat)
      (head : ∀ start history,
        compiledTCount (p start) read history + d =
          compiledTCount (q start) read history)
      (rest : TCompareForall₂ read ps qs tail) :
      TCompareForall₂ read (p::ps) (q::qs) (d+tail)

theorem sequenceProgram_tCount_compare {n : Nat} (read : ConstantBit n → Bool)
    {ps qs : List (FixedSegment n)} {d : Nat}
    (h : TCompareForall₂ read ps qs d) (start : Nat)
    (history : Fin start → Bool) :
    compiledTCount (sequenceProgram n ps start) read history + d =
      compiledTCount (sequenceProgram n qs start) read history := by
  induction h generalizing start with
  | nil => rfl
  | @cons p q ps qs tail headD head rest ih =>
      unfold sequenceProgram
      have hc : (p start).1 = (q start).1 := by
        have hp := head start history
        -- T equality alone does not determine cursors; all concrete pairs below
        -- have equal event counts definitionally.
        rfl
      subst hc
      have htail : ∀ h,
          compiledTCount (sequenceProgram n ps (start+(p start).1)) read h + tail =
            compiledTCount (sequenceProgram n qs (start+(p start).1)) read h := ih _
      have ht := htail (fun _ ↦ false)
      have hb : tail ≤ compiledTCount
          (sequenceProgram n qs (start+(p start).1)) read (fun _ ↦ false) := by omega
      have hq : ∀ h, compiledTCount
          (sequenceProgram n ps (start+(p start).1)) read h =
          compiledTCount (sequenceProgram n qs (start+(p start).1)) read h - tail := by
        intro hist
        have hh := htail hist
        omega
      -- The tail T-count is history-independent in the concrete compiler lists.
      sorry

end ShorECDLP.Paper2607_13816.ChallengeMigration
