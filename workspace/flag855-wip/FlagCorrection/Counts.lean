import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Pipeline
import ShorECDLP.Submission.Entrant.Streaming.Challenge.WindowCounts

namespace ShorECDLP.FlagCorrection

set_option maxHeartbeats 1000000

open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP.Compact

theorem splitZeroTest_tCount (flag : Wire) :
    ShorECDLP.tCount (splitZeroTest flag) = 14294 := by
  unfold splitZeroTest
  rw [tCount_append, tCount_append, tCount_append, tCount_append,
    computeEqConst_tCount _ _ _ _ (by simp [firstHalf, halfScratch]),
    zeroMask_tCount, dirtyMCX_tCount]
  norm_num [firstHalf, mcxVChainToffoliCost]

theorem flagQuerySource_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire) :
    (flagQuerySource read rows column control).tCount = 229369 := by
  rw [flagQuerySource, AdaptiveCircuit.relabel_tCount,
    batchQuery_tCount _ _ _ _ _ _ _ batchWindowTree_layout]
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at h
  omega

theorem flagQuerySource_measurementCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (column : Fin 8) (control : Wire) :
    (flagQuerySource read rows column control).measurementCount = 32767 := by
  rw [flagQuerySource, AdaptiveCircuit.relabel_measurementCount,
    unaryAction_measurementCount _ _ _ _ _ batchWindowTree_layout]
  have h := tableAddressTree_nodes pointLookupAddress 0 1
  change batchWindowTree.internalNodes + 1 = 32768 at h
  omega

private theorem adaptive_tCount_seq' (a b : AdaptiveCircuit) :
    (a.seq b).tCount = a.tCount + b.tCount := by
  simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b

private theorem adaptive_measurementCount_seq' (a b : AdaptiveCircuit) :
    (a.seq b).measurementCount = a.measurementCount + b.measurementCount := by
  induction a with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount]
  | unitary circuit next ih =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount, ih]
  | xMeasureReset target onFalse onTrue ihFalse ihTrue =>
      simp [AdaptiveCircuit.seq, AdaptiveCircuit.measurementCount, ihFalse, ihTrue,
        Nat.add_max_add_right, Nat.add_assoc]

theorem flagOpSource_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) :
    (flagOpSource read rows op).tCount =
      match op with | .query _ _ => 229369 | .test _ => 14294 := by
  cases op with
  | query column control => exact flagQuerySource_tCount read rows column control
  | test flag =>
      simp only [flagOpSource, AdaptiveCircuit.tCount, Nat.add_zero]
      exact splitZeroTest_tCount flag

theorem flagOpSource_measurementCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (op : FlagOp) :
    (flagOpSource read rows op).measurementCount =
      match op with | .query _ _ => 32767 | .test _ => 0 := by
  cases op with
  | query column control => exact flagQuerySource_measurementCount read rows column control
  | test flag => rfl

theorem flagCorrectionSource_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) : (flagCorrectionSource read rows).tCount = 5619208 := by
  simp [flagCorrectionSource, flagSources, flagSchedule, flagDetectSchedule,
    flagUpdateSchedule, flagClearSchedule, sequenceCircuit, adaptive_tCount_seq',
    flagOpSource_tCount, q]
  norm_num [AdaptiveCircuit.tCount]

theorem flagCorrectionSource_measurementCount {n : Nat}
    (read : ConstantBit n → Bool) (rows : Nat → Fin n) :
    (flagCorrectionSource read rows).measurementCount = 786408 := by
  simp [flagCorrectionSource, flagSources, flagSchedule, flagDetectSchedule,
    flagUpdateSchedule, flagClearSchedule, sequenceCircuit,
    adaptive_measurementCount_seq', flagOpSource_measurementCount, q]
  norm_num [AdaptiveCircuit.measurementCount]

theorem flagCorrectionProgram_count {n : Nat} (rows : Nat → Fin n) (start : Nat) :
    (flagCorrectionProgram rows start).1 = 786408 := by
  have h := compiled_count_of_run (flagCorrectionProgram rows start)
    (fun _ => false) (fun _ => false) _
    (flagCorrectionProgram_run (fun _ => false) rows start (fun _ => false))
  exact h.trans (flagCorrectionSource_measurementCount (fun _ => false) rows)

theorem flagPlacedProgram_count (w : OddWindow) (start : Nat) :
    (flagPlacedProgram w start).1 = 786408 :=
  flagCorrectionProgram_count _ _

theorem flagBatchedWindowCore_count (w : OddWindow) (start : Nat) :
    (flagBatchedWindowCore w start).1 = 31061154 := by
  simp only [flagBatchedWindowCore, flagBatchedWindowSegments, sequenceProgram,
    appendCompiled, sharedCoordinateProgram_count, sharedYNegateProgram_count,
    flagPlacedProgram_count]

theorem flagBatchedWindowSources_tCount (Q : Point) (w : OddWindow) :
    (sequenceCircuit (flagBatchedWindowSources Q w)).tCount = 515865602 := by
  unfold flagBatchedWindowSources
  rw [sequenceCircuit_four_tCount, (coordinate_numeric_counts _ _).1,
    windowYNegate_numeric_counts.1]
  change 510203526 + 21434 + (flagPlacedSource Q w).tCount + 21434 = _
  rw [flagPlacedSource, flagCorrectionSource_tCount]

theorem flagActualBatchedWindow_count (w : OddWindow) :
    (flagActualBatchedWindow w).count = 31061154 := by
  unfold flagActualBatchedWindow closedWindow
  change 0 + (flagBatchedWindowPrepared w 0).1 = 31061154
  rw [Nat.zero_add]
  have hp : (flagBatchedWindowPrepared w 0).1 = (flagBatchedWindowCore w 0).1 := by
    unfold flagBatchedWindowPrepared
    exact surroundCompiled_count _ _ _
  rw [hp, flagBatchedWindowCore_count]

theorem flagActualLeftWindows_count : axisCount flagActualLeftWindows = 465983101 := by
  unfold flagActualLeftWindows
  rw [axisCount, actualFirstWindow_count]
  rw [axisCount_constant _ 31061154]
  · simp
  · intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact flagActualBatchedWindow_count _

theorem flagActualRightWindows_count : axisCount flagActualRightWindows = 403795210 := by
  unfold flagActualRightWindows
  rw [axisCount_constant _ 31061154]
  · simp
  · intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    exact flagActualBatchedWindow_count _

theorem flagBatchedOuterPlan_stride : flagBatchedOuterPlan.stride = 869779165 := by
  have h := standardOuterPlan_lists_stride flagActualLeftWindows flagActualRightWindows
    flagActualLeftWindows_length flagActualRightWindows_length flagBatchedResetWires
  apply h.trans
  rw [flagActualLeftWindows_count, flagActualRightWindows_count,
    flagBatchedResetWires_length]

theorem flagBatchedOuterPlan_finalCursor :
    streamingRounds * flagBatchedOuterPlan.stride = 5218674990 := by
  rw [flagBatchedOuterPlan_stride]
  norm_num [streamingRounds]

end ShorECDLP.FlagCorrection
