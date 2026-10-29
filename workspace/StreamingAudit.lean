import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Challenge.PlacedBatch
import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation
import ShorECDLP.Submission.«2607_13816».Challenge.LookupPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.MatchingPhysical
import ShorECDLP.Submission.«2607_13816».Window.StreamTightSupport
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration
#check StreamingAssembly
#check OuterBudget
#check OuterBudget.assembly
#check actualBatchedWindow_run
#check placedBatchProgram_count
#check placedBatchState_finite
#check batchUnitary_infinity
#check windowYNegateState_pointWrite
#check coordinateProgram_tCount
#check gidneyProgram_tCount
#check divisionProgram_run
#check multiplicationProgram_tCount
#check registerCorrectionProgram_slots
#check OuterPlan.entry_records
#check OuterPlan.entry_reads
#check coefficientTable_length
#print axioms StreamingAssembly.certificate
#print axioms OuterBudget.resources
#print axioms actualBatchedWindow_run
#print axioms placedBatchSource_state
#print axioms placedBatchState_finite
#print axioms placedBatchSource_tCount
#print axioms coordinateProgram_tCount
#print axioms multiplicationProgram_run
#print axioms divisionProgram_run
#print axioms gidneyProgram_tCount
#print axioms registerCorrectionProgram_tCount
#print axioms OuterPlan.entry_reads
#print axioms coefficientTable_length

#check placedBatchState_pointWrite
#check placedBatchState_ready
#check placedBatchState_frame
#check signedLookupCoordinateProgram_coherent
#check negativeModularNegateState_involution
#check batchUnitary_fullFrame
#print axioms placedBatchState_pointWrite
#print axioms windowYNegateState_pointWrite
#print axioms negativeModularNegateState_involution
#print axioms batchUnitary_fullFrame
#print axioms streamRepeatedProgram_tight_certificate
