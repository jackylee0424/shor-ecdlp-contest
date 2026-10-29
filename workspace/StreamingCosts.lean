import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts

namespace ShorECDLP.Entrant.Streaming
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

/-- The measured correction compiler preserves the source T count for every history. -/
theorem batchedEndpointProgram_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    compiledTCount (batchedEndpointProgram rows base tree control paths start) read history =
      (batchSource read rows base tree control paths batchSchedule).tCount := by
  simp only [batchedEndpointProgram, compiledTCount, lookupProgram_tCount, batchOps_source]

theorem placedBatchProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (placedBatchProgram w start) (readConstant coefficientAt Q) history = 3784382 := by
  have h := relabelCompiled_tCount batchPlacement
    (batchedEndpointProgram (batchWindowRows w) 1024 batchWindowTree 836 pointLookupPath start)
    (batchSource (readConstant coefficientAt Q) (batchWindowRows w) 1024 batchWindowTree
      836 pointLookupPath batchSchedule) (readConstant coefficientAt Q) history
    (batchedEndpointProgram_tCount _ _ _ _ _ _ _ _)
  exact h.trans (placedBatchSource_tCount Q w)

/-- Counts of the totalized coordinate source, including the zero-test wrappers. -/
theorem signedCoordinate_counts (x y : Nat → Nat) :
    (signedLookupCoordinateProgram x y).tCount = 510203526 ∧
    (signedLookupCoordinateProgram x y).measurementCount = 30272702 := by
  have ha : pointLookupAdderPrimitives.toffoli = 2813 ∧
      pointLookupAdderPrimitives.phase = 0 ∧ pointLookupAdderPrimitives.measurements = 511 := by
    decide +kernel
  have hc := signedLookupCoordinateProgram_primitive x y
  have hn : (primitiveResources (signedLookupCoordinateProgram x y)).toffoli = 72886218 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).phase = 0 ∧
      (primitiveResources (signedLookupCoordinateProgram x y)).measurements = 30272702 := by
    rw [hc]
    simp only [signedCoordinatePrimitives, signedPointLookupPrimitives, pointLookupPrimitives,
      lookupWordPrimitives, pointLookupAddress, List.length_range', PrimitiveResources.add,
      ha.1, ha.2.1, ha.2.2]
    decide +kernel
  exact ⟨(primitiveResources_T_of_no_phase _ hn.2.1).trans (by rw [hn.1]), hn.2.2⟩

theorem sharedYNegateProgram_tCount (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedYNegateProgram w start) read history = windowYNegate.tCount := by
  simp only [sharedYNegateProgram, reindexCompiled, compiledTCount, reindexStraight_instantiate]
  exact yNegateProgram_tCount start _ history

/-- This equality is for the actual correction-bearing producer, at every record cursor. -/
theorem batchedWindowCore_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (batchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (batchedWindowSources Q w)).tCount := by
  apply sequenceProgram_tCount
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact sharedCoordinateProgram_tCount w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h
  · intro cursor h
    exact (placedBatchProgram_tCount w cursor Q h).trans (placedBatchSource_tCount Q w).symm
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h

end ShorECDLP.Entrant.Streaming
