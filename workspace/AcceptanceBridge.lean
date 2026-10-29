import ShorECDLP.Submission.«2607_13816».Window.RawDistribution
namespace ShorECDLP.Acceptance
open ShorECDLP.Paper2607_13816 ShorECDLP.Secp256k1
noncomputable section

lemma secpVerified_546 (Q : Point) (d : ℕ) (hn : Q ≠ 0) (hd : Q = d • G) :
    (546:ℝ)/1000 ≤ reducedVerifiedMass Q d := by
  rw [reducedVerifiedMass_eq Q d hd]
  apply secpCoverage_546 d
  intro hz
  have he := (secpCandidate_correct Q d hd (0:ZMod ShorECDLP.order)).mpr hz.symm
  simp only [ZMod.val_zero, zero_nsmul] at he
  exact hn he.symm

end
end ShorECDLP.Acceptance
