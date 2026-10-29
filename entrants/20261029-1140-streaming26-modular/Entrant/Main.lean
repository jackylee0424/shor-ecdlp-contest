import ShorECDLP.Submission.Entrant.Streaming.Challenge.FinalCertificate

/-!
Construction and proofs from VerifiedQC/ShorECDLP,
lamport/challenge-final-certificate @ b46e337 (Apache-2.0).
The round count is reduced from 56 to 26 using the upstream per-round
0.163 acceptance bound. The entry and decoder share streamingRounds.
-/

namespace ShorECDLP.Entrant
open ShorECDLP.Challenge ShorECDLP.Paper2607_13816.ChallengeMigration

def entry := streamingEntry

def layout := batchedOuterPlan.layoutForStreaming

def bounds := streamingBounds

theorem certificate : Certificate officialLimits layout entry bounds :=
  streamingEntry_certificate_unconditional

end ShorECDLP.Entrant
