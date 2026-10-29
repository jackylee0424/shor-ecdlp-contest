#!/usr/bin/env python3
"""Install our proved acceptance theorem into a freshly ported modular entrant.

Run from the lab after port_upstream.py --rounds 6, before package_streaming.py.
The scratch proof is combined from lab files; only Entrant/ is changed in bench.
"""
from pathlib import Path
import subprocess

lab = Path(__file__).resolve().parent.parent
bench = Path.home() / 'shorecdlp'
target = bench / 'ShorECDLP/Submission/Entrant/Streaming'
subprocess.run(['python3', str(lab / 'workspace/acceptance_check.py')], cwd=lab, check=True)
contribution = target / 'Contributions/UniformAcceptance.lean'
contribution.parent.mkdir(parents=True, exist_ok=True)
contribution.write_text((lab / 'workspace/AcceptanceCheck.lean').read_text())
bridge = target / 'Challenge/DecoderBridge.lean'
s = bridge.read_text()
s = 'import ShorECDLP.Submission.Entrant.Streaming.Contributions.UniformAcceptance\n' + s
s = s.replace('(163:ℝ)/1000', '(546:ℝ)/1000')
s = s.replace('  exact secpSuccessBound_numeric.trans (reducedPhysicalVerifiedMass_lower Q hG hQ hrQ d hQd)',
'''  rw [reducedPhysicalVerifiedMass_eq Q hG hQ hrQ d hQd]
  exact ShorECDLP.Acceptance.secpVerified_546 Q d hQ hQd''')
bridge.write_text(s)
final = target / 'Challenge/FinalCertificate.lean'
s = final.read_text().replace('(163:ℝ)/1000', '(546:ℝ)/1000')
final.write_text(s)
print('Installed our uniform acceptance theorem and replaced the round-success bound with 546/1000.')
