import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStages

/-!
# Clean-lane inventory for Brief 13

This file records only consequences of the frontier's public validity and EEA-output
contracts.  It deliberately does not assume that any data-dependent EEA lane happens to
be zero on sampled inputs.
-/

namespace ShorECDLP.Paper2607_13816.MulClean

open Classical
set_option maxRecDepth 100000

/-- Clean lanes outside a 256-bit Horner destination at an ordinary Figure-14/15 boundary. -/
def boundaryPool : List Wire := List.range 7 ++ List.range' 519 61

/-- The zero-allowed flag is also clean at the square call, which is outside the wrappers. -/
def squarePool : List Wire := boundaryPool ++ [837]

/--
Clean lanes outside the work destination immediately after the forward EEA.  The first
three come from `Clean (List.range' 4 259)` after removing destination `7..262`; label 559
and `sharedScratch = 558 :: 560..579` come from the other two output conjuncts.
-/
def postEeaPool : List Wire :=
  List.range' 4 3 ++ List.range' 558 22

theorem boundaryPool_eq :
    boundaryPool = [0, 1, 2, 3, 4, 5, 6] ++ List.range' 519 61 := by
  decide +kernel

theorem postEeaPool_eq :
    postEeaPool = [4, 5, 6] ++ List.range' 558 22 := by
  decide +kernel

theorem boundaryPool_nodup : boundaryPool.Nodup := by
  decide +kernel

theorem squarePool_nodup : squarePool.Nodup := by
  decide +kernel

theorem postEeaPool_nodup : postEeaPool.Nodup := by
  decide +kernel

theorem boundaryPool_length : boundaryPool.length = 68 := by
  decide +kernel

theorem squarePool_length : squarePool.length = 69 := by
  decide +kernel

theorem postEeaPool_length : postEeaPool.length = 25 := by
  decide +kernel

private theorem mem_sharedScratch_of_range {w : Wire}
    (hlo : 558 ≤ w) (hhi : w < 580) (hne : w ≠ 559) :
    w ∈ indexedStepProductionRegisters.sharedScratch := by
  interval_cases w <;> simp at hne <;> decide +kernel

theorem boundaryPool_clean (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Clean boundaryPool s := by
  intro w hw
  apply hs.1 w
  simp only [boundaryPool, List.mem_append, List.mem_range, List.mem_range'_1] at hw ⊢
  omega

theorem squarePool_clean (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Clean squarePool s := by
  intro w hw
  simp only [squarePool, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact boundaryPool_clean s hs w hw
  · exact hs.2.1

theorem postEeaPool_clean (s : BasisState)
    (hclean : Clean (List.range' 0 263 ++ List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s) < ShorECDLP.p) :
    Clean postEeaPool (secp256k1EEAOutputIdealState s) := by
  have ho := secp256k1EEAOutputIdealState_correct s hclean hx hxp
  intro w hw
  simp only [postEeaPool, List.mem_append, List.mem_range'_1] at hw
  rcases hw with hw | hw
  · exact ho.2.2.1 w (by simp only [List.mem_range'_1]; omega)
  · obtain ⟨hlo, hhi⟩ := hw
    by_cases he : w = 559
    · subst w
      exact ho.2.2.2.1
    · exact ho.2.2.2.2 w (mem_sharedScratch_of_range hlo hhi he)

end ShorECDLP.Paper2607_13816.MulClean
