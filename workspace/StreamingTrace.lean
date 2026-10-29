import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts

namespace ShorECDLP.Entrant.Streaming
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] signedLookupCoordinateProgram primitiveResources
  batchedWindowCore batchedWindowPrepared sharedCoordinateProgram yNegateProgram placedBatchProgram windowYNegate

/-- The measured correction compiler preserves the source T count for every history. -/
#eval do (← IO.getStdout).flush
theorem batchedEndpointProgram_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    compiledTCount (batchedEndpointProgram rows base tree control paths start) read history =
      (batchSource read rows base tree control paths batchSchedule).tCount := by
  simp only [batchedEndpointProgram, compiledTCount, lookupProgram_tCount, batchOps_source]

#eval do (← IO.getStdout).flush
theorem placedBatchProgram_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    compiledTCount (placedBatchProgram w start) (readConstant coefficientAt Q) history = 3784382 := by
  unfold placedBatchProgram
  have h := relabelCompiled_tCount batchPlacement
    (batchedEndpointProgram (batchWindowRows w) 1024 batchWindowTree 836 pointLookupPath start)
    (batchSource (readConstant coefficientAt Q) (batchWindowRows w) 1024 batchWindowTree
      836 pointLookupPath batchSchedule) (readConstant coefficientAt Q) history
    (batchedEndpointProgram_tCount _ _ _ _ _ _ _ _)
  exact h.trans (placedBatchSource_tCount Q w)

/-- Counts of the totalized coordinate source, including the zero-test wrappers. -/
#check "before signedCoordinate_counts"
#eval do (← IO.getStdout).flush
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
  constructor
  · rw [primitiveResources_T_of_no_phase _ hn.2.1, hn.1]
  · simpa only [primitiveResources] using hn.2.2

#check "before sharedYNegateProgram_tCount"
#eval do (← IO.getStdout).flush
theorem sharedYNegateProgram_tCount (w : OddWindow) (start : Nat)
    (read : ConstantBit 983040 → Bool) (history : Fin start → Bool) :
    compiledTCount (sharedYNegateProgram w start) read history = windowYNegate.tCount := by
  simp only [sharedYNegateProgram, reindexCompiled, compiledTCount, reindexStraight_instantiate]
  exact yNegateProgram_tCount start _ history

/-- This equality is for the actual correction-bearing producer, at every record cursor. -/
#check "before batchedWindowCore_tCount"
#eval do (← IO.getStdout).flush
theorem batchedWindowCore_tCount (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (batchedWindowCore w start) (readConstant coefficientAt Q) history =
      (sequenceCircuit (batchedWindowSources Q w)).tCount := by
  unfold batchedWindowCore
  apply sequenceProgram_tCount
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ .nil)))
  · intro cursor h; exact sharedCoordinateProgram_tCount w cursor Q hQ h
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h
  · intro cursor h
    exact (placedBatchProgram_tCount w cursor Q h).trans (placedBatchSource_tCount Q w).symm
  · intro cursor h; exact sharedYNegateProgram_tCount w cursor _ h


/-- Extra sign conjugations use the same measured modular-negation counts. -/
#check "before windowYNegate_counts"
#eval do (← IO.getStdout).flush
theorem windowYNegate_counts : windowYNegate.tCount = 21434 ∧
    windowYNegate.measurementCount = 1022 := by
  have h := negativeControlledModularNegate_resources (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558
  have hm : constantBits 256 ShorECDLP.p = secp256k1ModulusBits := by decide +kernel
  rw [hm] at h
  have hc := controlledModularNegate256_counts (List.range' 580 256) (List.range' 7 256)
    854 559 560 561 558 (by simp) (by simp)
  simpa only [windowYNegate, hm] using And.intro (h.1.trans hc.1) (h.2.trans hc.2)

#check "before batchedWindowCore_tCount"
#check "before batchedWindowCore_tCount_exact"
#eval do (← IO.getStdout).flush
theorem batchedWindowCore_tCount_exact (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    compiledTCount (batchedWindowCore w start) (readConstant coefficientAt Q) history = 514030776 := by
  rw [batchedWindowCore_tCount w start Q hQ history]
  simp only [batchedWindowSources, sequenceCircuit, adaptive_tCount_seq,
    (signedCoordinate_counts _ _).1, windowYNegate_counts.1, placedBatchSource_tCount,
    AdaptiveCircuit.tCount]

/-- The legacy reset list omits the zero-test flag used by totalized division. -/
#eval do (← IO.getStdout).flush
theorem zeroFlag_not_reset : (837 : Wire) ∉ batchedResetWires := by
  simp [batchedResetWires, resetWires]

end ShorECDLP.Entrant.Streaming
