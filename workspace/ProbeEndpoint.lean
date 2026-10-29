import ShorECDLP.Submission.Entrant.Streaming.FlagCorrection.Pure

namespace ShorECDLP.FlagCorrection
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1
open ShorECDLP.Paper2607_13816 ShorECDLP.Paper2607_13816.ChallengeMigration

#check nsmul_eq_nsmul_iff_modEq
#check zsmul_eq_zsmul_iff
#check zsmul_eq_zsmul_iff'
#check Nat.ModEq.eq_of_lt_of_lt
#check Nat.ModEq.eq_of_lt_of_lt
#check Nat.sub_nsmul
#check sub_nsmul
#check add_nsmul

example {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (row : Fin n)
    {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) : True := by
  have hp := readEndpointWords_pairs coeffs Q row
  rw [hrow, protectedExceptionPairs_eq hC] at hp
  simp [fixedExceptionPairs, fixedExceptionInputs] at hp
  trace_state
  trivial

end ShorECDLP.FlagCorrection
