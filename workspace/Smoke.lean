import ShorECDLP.Submission.Entrant.Main

/-! Smoke test for formal-tools/check.sh: the entrant's declared bounds. -/
open ShorECDLP

#check @Entrant.certificate
#eval Entrant.bounds.qubits * Entrant.bounds.tModel
