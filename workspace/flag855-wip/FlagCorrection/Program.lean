import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Query
import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Zero
import ShorECDLP.Submission.«2607_13816».Challenge.Sequence

namespace ShorECDLP.FlagCorrection

set_option maxHeartbeats 1000000

open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

def flagQueryOps {n : Nat} (rows : Nat → Fin n) (column : Fin 8) : List (LookupOp n) :=
  unaryLookupOps
    (fun l q => batchLeaf (rows l) 1024 q (oneColumn column))
    batchWindowTree 836 pointLookupPath

def flagQueryProgram {n : Nat} (rows : Nat → Fin n) (column : Fin 8)
    (control : Wire) (start : Nat) :
    (count : Nat) × Straight n start (start + count) :=
  relabelCompiled (queryPlacement control)
    ⟨lookupMeasurements (flagQueryOps rows column),
      lookupProgram n (flagQueryOps rows column) start⟩

attribute [local irreducible] batchWindowTree in
theorem flagQueryProgram_run {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire) (start : Nat)
    (history : Fin start → Bool) :
    compiledRun (flagQueryProgram rows column control start) read history =
      (flagQuerySource read rows column control).run := by
  unfold flagQueryProgram flagQuerySource
  apply relabelCompiled_run
  unfold compiledRun
  unfold flagQueryOps
  rw [lookupProgram_run, unaryLookupOps_circuit]
  have hleaf :
      (fun l q => (batchLeaf (rows l) 1024 q (oneColumn column)).flatMap
        (TemplateGate.instantiate read)) =
      (fun l q => batchLeafCircuit read (rows l) 1024 q (oneColumn column)) := by
    funext l q
    exact batchLeaf_source read (rows l) 1024 q (oneColumn column)
  rw [hleaf]

theorem flagQueryProgram_count {n : Nat} (rows : Nat → Fin n) (column : Fin 8)
    (control : Wire) (start : Nat) :
    (flagQueryProgram rows column control start).1 = 32767 := by
  simp only [flagQueryProgram, relabelCompiled, flagQueryOps]
  rw [unaryLookupOps_measurements _ _ _ _ batchWindowTree_layout]
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  have h' : (tableAddressTree pointLookupAddress 0 1).internalNodes + 1 = 32768 := by
    simpa [pointLookupAddress] using h
  change (tableAddressTree pointLookupAddress 0 1).internalNodes = 32767
  omega

inductive FlagOp where
  | query (column : Fin 8) (control : Wire)
  | test (flag : Fin 4)

def q (column : Nat) (hc : column < 8) (control : Wire) : FlagOp :=
  .query ⟨column, hc⟩ control

def flagDetectSchedule : List FlagOp :=
  [q 0 (by omega) 836, .test 0,
   q 0 (by omega) 836, q 1 (by omega) 836, .test 1,
   q 1 (by omega) 836, q 2 (by omega) 836, .test 2,
   q 2 (by omega) 836, q 3 (by omega) 836, .test 3]

def flagUpdateSchedule : List FlagOp :=
  [q 0 (by omega) 0, q 4 (by omega) 0,
   q 1 (by omega) 1, q 5 (by omega) 1,
   q 2 (by omega) 2, q 6 (by omega) 2,
   q 3 (by omega) 3, q 7 (by omega) 3]

def flagClearSchedule : List FlagOp :=
  [q 3 (by omega) 836, q 4 (by omega) 836, .test 0,
   q 4 (by omega) 836, q 5 (by omega) 836, .test 1,
   q 5 (by omega) 836, q 6 (by omega) 836, .test 2,
   q 6 (by omega) 836, q 7 (by omega) 836, .test 3,
   q 7 (by omega) 836]

/-- The conservative schedule uses separate one-column traversals.  The paired-column
optimization can later fuse adjacent queries without changing this logical order. -/
def flagSchedule : List FlagOp :=
  flagDetectSchedule ++ flagUpdateSchedule ++ flagClearSchedule

def flagOpProgram {n : Nat} (rows : Nat → Fin n) (op : FlagOp) : FixedSegment n :=
  match op with
  | .query column control => flagQueryProgram rows column control
  | .test flag => fun _ => ⟨0, literalProgram (splitZeroTest flag.val)⟩

noncomputable def flagOpSource {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) : FlagOp → AdaptiveCircuit
  | .query column control => flagQuerySource read rows column control
  | .test flag => .unitary (splitZeroTest flag.val) .done

def flagSegments {n : Nat} (rows : Nat → Fin n) : List (FixedSegment n) :=
  flagSchedule.map (flagOpProgram rows)

noncomputable def flagSources {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) : List AdaptiveCircuit :=
  flagSchedule.map (flagOpSource read rows)

def flagCorrectionProgram {n : Nat} (rows : Nat → Fin n) (start : Nat) :
    (count : Nat) × Straight n start (start + count) :=
  sequenceProgram n (flagSegments rows) start

noncomputable def flagCorrectionSource {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) : AdaptiveCircuit :=
  sequenceCircuit (flagSources read rows)

theorem flagOpProgram_run {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) (start : Nat) (history : Fin start → Bool) :
    compiledRun (flagOpProgram rows op start) read history =
      (flagOpSource read rows op).run := by
  cases op with
  | query column control => exact flagQueryProgram_run read rows column control start history
  | test flag => exact literalProgram_run _ read history

theorem flagCorrectionProgram_run {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (start : Nat) (history : Fin start → Bool) :
    compiledRun (flagCorrectionProgram rows start) read history =
      (flagCorrectionSource read rows).run := by
  unfold flagCorrectionProgram flagCorrectionSource flagSegments flagSources
  apply sequenceProgram_run
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro op hop cursor h
  exact flagOpProgram_run read rows op cursor h

theorem flagSchedule_queries :
    (flagSchedule.filter (fun op => match op with | .query _ _ => true | _ => false)).length = 24 := by
  rfl

theorem flagSchedule_tests :
    (flagSchedule.filter (fun op => match op with | .test _ => true | _ => false)).length = 8 := by
  rfl

end ShorECDLP.FlagCorrection
