import ShorECDLP.Submission.Entrant.Streaming.Dirty.Challenge.BatchedEndpoint
import ShorECDLP.Submission.«2607_13816».Challenge.SharedTable
import ShorECDLP.Submission.«2607_13816».Challenge.Relabel
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
namespace ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
/-- Exchange the component's data word with the actual accumulator, leaving the
endpoint bank and all address/control/path wires in place. -/
def batchPlacementFn (w : Wire) : Wire :=
  if 3589 ≤ w ∧ w < 3845 then 263 + (w-3589)
  else if 3845 ≤ w ∧ w < 4101 then 580 + (w-3845)
  else if w = 4101 then 838
  else if 263 ≤ w ∧ w < 519 then 3589 + (w-263)
  else if 580 ≤ w ∧ w < 836 then 3845 + (w-580)
  else if w = 838 then 4101 else w

theorem batchPlacementFn_involutive : Function.Involutive batchPlacementFn := by
  intro w
  generalize hv : batchPlacementFn w = v
  unfold batchPlacementFn at hv
  split_ifs at hv <;> subst v <;> unfold batchPlacementFn <;> split_ifs <;> dsimp only [Wire] at * <;> omega

def batchPlacement : Wire ≃ Wire :=
  ⟨batchPlacementFn,batchPlacementFn,batchPlacementFn_involutive,batchPlacementFn_involutive⟩

def accumulatorPort (i : Fin 513) : Wire :=
  if i.val < 256 then 263+i.val else if i.val < 512 then 580+(i.val-256) else 838

theorem batchPlacement_data (i : Fin 513) :
    batchPlacement (batchWord 1024 5 i) = accumulatorPort i := by
  change batchPlacementFn (1024+513*5+i.val) = _
  unfold batchPlacementFn accumulatorPort
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem batchPlacement_endpoints (w : Wire) (lo : 1024 ≤ w) (hi : w < 3589) :
    batchPlacement w = w := by
  change batchPlacementFn w = w
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem batchPlacement_high (w : Wire) (lo : 4102 ≤ w) : batchPlacement w = w := by
  change batchPlacementFn w = w
  unfold batchPlacementFn
  split_ifs <;> dsimp only [Wire] at * <;> omega

def batchWindowRows (w : OddWindow) (label : Nat) : Fin 983040 :=
  windowIndex w ⟨label % 32768,Nat.mod_lt _ (by decide)⟩

def batchWindowTree : UnaryActionTree := tableAddressTree pointLookupAddress 0 1

theorem batchWindowTree_layout : batchWindowTree.Layout 836 pointLookupPath :=
  tableAddressTree_layout _ _ _ _ _ (by decide) (by decide)

def placedBatchProgramRaw (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  relabelCompiled batchPlacement
    (batchedEndpointProgram (batchWindowRows w) 1024 batchWindowTree 836 pointLookupPath start)

theorem placedBatchProgramRaw_count (w : OddWindow) (start : Nat) :
    (placedBatchProgramRaw w start).1 = 458738 := by
  simp only [placedBatchProgramRaw, relabelCompiled]
  rw [batchedEndpointProgram_count _ _ _ _ _ _ batchWindowTree_layout]
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at h
  omega

def placedBatchStraight (w : OddWindow) (start : Nat) :
    Straight 983040 start (start + 458738) :=
  let p := placedBatchProgramRaw w start
  castFinish (congrArg (fun count => start + count)
    (placedBatchProgramRaw_count w start)) p.2

def placedBatchProgram (w : OddWindow) (start : Nat) :
    (count : Nat) × Straight 983040 start (start+count) :=
  ⟨458738, placedBatchStraight w start⟩

noncomputable def placedBatchSource (Q : Point) (w : OddWindow) : AdaptiveCircuit :=
  (batchSource (readConstant coefficientAt Q) (batchWindowRows w) 1024
    batchWindowTree 836 pointLookupPath batchSchedule).relabel batchPlacement

theorem placedBatchStraight_run (w : OddWindow) (start : Nat) (Q : Point)
    (history : Fin start → Bool) :
    ((placedBatchStraight w start).instantiate (readConstant coefficientAt Q) history).run =
      (placedBatchSource Q w).run := by
  simp only [placedBatchStraight, castFinish_instantiate]
  simp only [placedBatchProgramRaw, placedBatchSource, relabelCompiled,
    relabelStraight_instantiate, AdaptiveCircuit.run_relabel,
    batchedEndpointProgram, lookupProgram_run, batchOps_source]

theorem placedBatchProgram_count (w : OddWindow) (start : Nat) :
    (placedBatchProgram w start).1 = 458738 := rfl

end ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty
