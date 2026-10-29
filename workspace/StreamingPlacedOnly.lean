import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts

namespace ShorECDLP.Entrant.Streaming
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] signedLookupCoordinateProgram primitiveResources batchSource batchedEndpointProgram

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
  simp only [placedBatchProgram, relabelCompiled, compiledTCount,
    relabelStraight_instantiate, AdaptiveCircuit.relabel_tCount]
  rw [show ((batchedEndpointProgram (batchWindowRows w) 1024 batchWindowTree 836
    pointLookupPath start).2.instantiate (readConstant coefficientAt Q) history).tCount =
    (batchSource (readConstant coefficientAt Q) (batchWindowRows w) 1024 batchWindowTree
      836 pointLookupPath batchSchedule).tCount from batchedEndpointProgram_tCount _ _ _ _ _ _ _ _]
  simpa only [placedBatchSource, AdaptiveCircuit.relabel_tCount] using placedBatchSource_tCount Q w


end ShorECDLP.Entrant.Streaming
