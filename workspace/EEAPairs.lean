import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep

namespace ShorECDLP.Paper2607_13816
open Quantum

def adjacentEqualCCX (gs : Circuit) : Nat :=
  (gs.zip gs.tail).foldl (fun count pair =>
    count + if pair.1 = pair.2 then match pair.1 with | .CCX _ _ _ => 1 | _ => 0 else 0) 0

#eval List.ofFn (fun T : Fin 16 =>
  adjacentEqualCCX (indexedStepUnitary indexedStepProductionRegisters 256 (T+1)))

end ShorECDLP.Paper2607_13816
