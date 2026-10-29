import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep

namespace ShorECDLP.Paper2607_13816
open Quantum

def adjacentEqualCCX (gs : Circuit) : Nat :=
  (gs.zip gs.tail).foldl (fun count pair =>
    count + if pair.1 = pair.2 then match pair.1 with | .CCX _ _ _ => 1 | _ => 0 else 0) 0

#eval List.ofFn (fun T : Fin 16 =>
  adjacentEqualCCX (indexedStepUnitary indexedStepProductionRegisters 256 (T+1)))

#eval adjacentEqualCCX (blockAForward indexedStepProductionRegisters)
#eval List.ofFn (fun T : Fin 4 => adjacentEqualCCX
  (blockCForward indexedStepProductionRegisters ++
    blockDForward indexedStepProductionRegisters
      (certifiedActiveWindows 256 (T+1)).quotientSwap))
#eval adjacentEqualCCX (blockFForward indexedStepProductionRegisters)

def ePrefix (r : IndexedStepRegisters) : Circuit :=
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
  computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
  prepareLatestPaperTBoundary r.tBoundary 256

def eMiddle (r : IndexedStepRegisters) : Circuit :=
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
  computeControl [r.phase1,r.terminal] 1 r.control r.blockScratch ++
  computeControl [r.phase2,r.sign] 2 r.terminal r.blockScratch ++
  [.CX r.phase1 r.sign] ++ computeControl [r.phase1] 1 r.control r.blockScratch

def eSuffix (r : IndexedStepRegisters) : Circuit :=
  computeControl [r.phase1] 1 r.control r.blockScratch ++
  restoreLatestPaperTBoundary r.tBoundary 256

#eval adjacentEqualCCX (ePrefix indexedStepProductionRegisters)
#eval adjacentEqualCCX (eMiddle indexedStepProductionRegisters)
#eval adjacentEqualCCX (eSuffix indexedStepProductionRegisters)

def adjacentCCXPairs (gs : Circuit) : List (Nat × Gate) :=
  ((List.range gs.length).zip (gs.zip gs.tail)).filterMap (fun pair =>
    if pair.2.1 = pair.2.2 then
      match pair.2.1 with | g@(.CCX _ _ _) => some (pair.1, g) | _ => none
    else none)

#eval adjacentCCXPairs (ePrefix indexedStepProductionRegisters)
#eval adjacentCCXPairs (eSuffix indexedStepProductionRegisters)

end ShorECDLP.Paper2607_13816
