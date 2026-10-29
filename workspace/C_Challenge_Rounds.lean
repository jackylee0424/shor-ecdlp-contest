import ShorECDLP.Submission.«2607_13816».Challenge.Outer

namespace ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty
open Quantum ShorECDLP.Challenge

/-- Shared repetition count for the entry, decoder, resource and success proofs. -/
def streamingRounds : Nat := 6

def OuterPlan.entryForStreaming (coefficients : List PointCoeff)
    (p : OuterPlan coefficients.length) : StraightEntry :=
  ⟨coefficients, streamingRounds*p.stride,
    castFinish (by omega) (p.repeat streamingRounds 0)⟩

def OuterPlan.positionsForStreaming {n : Nat} (p : OuterPlan n)
    (r : Fin streamingRounds) : TrialPositions legacyDecoderParams where
  left := ⟨(axisPositions p.left.toList (r.val*p.stride)).toArray,
    by simp [axisPositions_length, legacyDecoderParams]⟩
  right := ⟨(axisPositions p.right.toList (r.val*p.stride+axisCount p.left.toList)).toArray,
    by simp [axisPositions_length, legacyDecoderParams]⟩

def OuterPlan.layoutForStreaming {n : Nat} (p : OuterPlan n) : DecodeLayout :=
  ⟨.wrappedShift, legacyDecoderParams, List.ofFn (OuterPlan.positionsForStreaming p),
    by simp [streamingRounds]⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty
