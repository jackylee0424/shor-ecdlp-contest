import ShorECDLP.Submission.Entrant.Streaming.Dirty.Challenge.BatchTemplate

namespace ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty

#check placedBatchStraight_wellFormed
#print placedBatchProgram

example (w : OddWindow) (start : Nat) :
    (placedBatchProgram w start).2.WellFormed := by
  have he : (placedBatchProgram w start).2 = placedBatchStraight w start := rfl
  rw [he]
  exact placedBatchStraight_wellFormed w start

end ShorECDLP.Paper2607_13816.ChallengeMigration.Dirty
