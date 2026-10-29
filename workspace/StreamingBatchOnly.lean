import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Window.LookupPrimitiveCounts

#check "imports loaded"
#eval do (← IO.getStdout).flush
namespace ShorECDLP.Entrant.Streaming
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
attribute [local irreducible] signedLookupCoordinateProgram primitiveResources

/-- The measured correction compiler preserves the source T count for every history. -/
theorem batchedEndpointProgram_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (start : Nat) (history : Fin start → Bool) :
    compiledTCount (batchedEndpointProgram rows base tree control paths start) read history =
      (batchSource read rows base tree control paths batchSchedule).tCount := by
  simp only [batchedEndpointProgram, compiledTCount, lookupProgram_tCount, batchOps_source]


end ShorECDLP.Entrant.Streaming
