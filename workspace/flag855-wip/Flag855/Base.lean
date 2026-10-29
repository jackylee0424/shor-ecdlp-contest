import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Pipeline

namespace ShorECDLP.Paper2607_13816.ChallengeMigration.Flag855
set_option maxHeartbeats 1000000

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.FlagCorrection

def actualBatchedWindow := flagActualBatchedWindow
def actualLeftWindows := flagActualLeftWindows
def actualRightWindows := flagActualRightWindows
def batchedResetWires := flagBatchedResetWires
def batchedOuterPlan := flagBatchedOuterPlan
noncomputable def actualBatchedWindowState := flagActualBatchedWindowState

theorem actualBatchedWindow_run (w : OddWindow) (start : Nat) (Q : Point)
    (hQ : order • Q = 0) (history : Fin start → Bool) :
    (((actualBatchedWindow w).program start).instantiate
      (readConstant coefficientAt Q) history).run =
      ((flagBatchedWindowPreparedSource Q w).relabel
        (windowAddressPerm 855 (by decide))).run :=
  flagActualBatchedWindow_run w start Q hQ history

theorem actualBatchedWindow_coherent (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (start : Nat) (history : Fin start → Bool) :
    CoherentlyImplementsOn (((actualBatchedWindow w).program start).instantiate
      (readConstant coefficientAt Q) history)
      (Finsupp.lmapDomain ℂ ℂ (actualBatchedWindowState Q w))
      BatchedWindowValid :=
  flagActualBatchedWindow_coherent Q hQ hn w start history

theorem actualBatchedWindowState_selected (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedPointReady s)
    (P : Point) (hP : pointStateCoordinates s = fig14PointEncoding P) :
    actualBatchedWindowState Q w s = pointWrite
      (P + if s 870 then windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))
        else -windowPoint Q w (signedTableAddress 32768 (windowRawDigit 0 s))) s :=
  flagActualBatchedWindowState_selected Q hQ hn w s hs P hP

theorem actualBatchedWindowState_valid (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s) :
    BatchedWindowValid (actualBatchedWindowState Q w s) :=
  flagActualBatchedWindowState_valid Q hQ hn w s hs

theorem actualBatchedWindowState_frame (Q : Point) (hQ : order • Q = 0)
    (hn : Q ≠ 0) (w : OddWindow) (s : BasisState) (hs : BatchedWindowValid s)
    (v : Wire) (hv : v ∉ pointLogicalWires) :
    actualBatchedWindowState Q w s v = s v :=
  flagActualBatchedWindowState_frame Q hQ hn w s hs v hv

theorem actualLeftWindows_length : actualLeftWindows.length = 16 :=
  flagActualLeftWindows_length

theorem actualRightWindows_length : actualRightWindows.length = 13 :=
  flagActualRightWindows_length

theorem batchedResetWires_length : batchedResetWires.length = 854 :=
  flagBatchedResetWires_length

end ShorECDLP.Paper2607_13816.ChallengeMigration.Flag855
