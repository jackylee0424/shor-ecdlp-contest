#!/usr/bin/env python3
"""Port only added upstream Lean modules; preserve imports of protected modules.

With --rounds 26, also apply the local round-count and decoder-layout adaptation.
This intentionally overwrites the ported modules, so save local improvements
before updating the upstream ref. Main.lean is managed separately.
"""
import argparse
from pathlib import Path
import re
import subprocess


def reduce_rounds(target):
    """Adapt the eight round-dependent files, retaining the decoder's 56 cap."""
    names = ('FinalCertificate', 'FixedWord', 'RepeatEvent', 'ResourceCertificate',
             'UniformT', 'WindowBudget', 'WindowCounts', 'WindowSlots')
    for name in names:
        path = target / 'Challenge' / f'{name}.lean'
        source = path.read_text()
        # This generic lemma expresses the protected DecodeLayout trial cap.
        source = source.replace('positions.length ≤ 56', 'positions.length ≤ TRIAL_CAP')
        source = re.sub(r'\b56\b', 'streamingRounds', source)
        source = source.replace('TRIAL_CAP', '56')
        source = source.replace('806028979896', '374227740666')
        source = source.replace('48194018992', '22375794532')
        source = source.replace('batchedOuterPlan.layout', 'batchedOuterPlan.layoutForStreaming')
        source = source.replace('p.layout', 'p.layoutForStreaming')
        source = source.replace('OuterPlan.layout,', 'OuterPlan.layoutForStreaming,')
        source = source.replace('OuterPlan.positions', 'OuterPlan.positionsForStreaming')
        source = source.replace('p.positions', 'p.positionsForStreaming')
        if name == 'RepeatEvent':
            # The single-round acceptance predicate still uses protected positions.
            start = source.index('private theorem roundAccept_zero')
            end = source.index('theorem actualRoundFixedAccept_eq', start)
            source = (source[:start] + source[start:end].replace(
                'positionsForStreaming', 'positions') + source[end:])
        if name == 'FixedWord':
            source = source.replace('p.entry coefficients', 'p.entryForStreaming coefficients')
            source = source.replace('OuterPlan.entry,', 'OuterPlan.entryForStreaming,')
        if name == 'FinalCertificate':
            source = source.replace('norm_num [independentRetrySuccessProbability]',
                                    'norm_num [independentRetrySuccessProbability, streamingRounds]')
        if name == 'WindowCounts':
            source = source.replace('rw [batchedOuterPlan_stride]',
                                    'rw [batchedOuterPlan_stride]\n  norm_num [streamingRounds]')
        if name == 'WindowBudget':
            # The original historical observation is false for the reduced entry.
            source = re.sub(r'/--[^/]*?-/\s*theorem batchedOuterPlan_exceeds_old_measurement_limit.*?\n(?=theorem batchedOuterPlan_measurements_fit)',
                            '', source, flags=re.S)
        source = source.replace('streamingRounds-round', '26-round')
        source = source.replace('of streamingRounds rounds', 'of 26 rounds')
        source = 'import ShorECDLP.Submission.Entrant.Streaming.Challenge.Rounds\n' + source
        path.write_text(source)
    (target / 'Challenge/Rounds.lean').write_text('''import ShorECDLP.Submission.«2607_13816».Challenge.Outer

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- Shared repetition count for the entry, decoder, resource and success proofs. -/
def streamingRounds : Nat := 26

def OuterPlan.entryForStreaming (coefficients : List PointCoeff)
    (p : OuterPlan coefficients.length) : StraightEntry :=
  ⟨coefficients, streamingRounds*p.stride,
    castFinish (by omega) (p.repeat streamingRounds 0)⟩

def OuterPlan.positionsForStreaming {n : Nat} (p : OuterPlan n)
    (r : Fin streamingRounds) : TrialPositions legacyDecoderParams where
  left := ⟨(axisPositions p.left.toList (r.val*p.stride)).toArray,
    by simp [axisPositions_length, legacyDecoderParams]⟩
  right := ⟨(axisPositions p.right.toList (r.val*p.stride+axisCount p.left.toList)).toArray,
    by simp [axisPositions_length, legacyDecoderParams]⟩

def OuterPlan.layoutForStreaming {n : Nat} (p : OuterPlan n) : DecodeLayout :=
  ⟨.wrappedShift, legacyDecoderParams, List.ofFn p.positionsForStreaming,
    by simp [streamingRounds]⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration
''')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bench', type=Path, default=Path.home() / 'shorecdlp')
    parser.add_argument('--base', default='origin/master')
    parser.add_argument('--upstream', default='upstream/lamport/challenge-final-certificate')
    parser.add_argument('--rounds', type=int, choices=(26, 56), default=56)
    args = parser.parse_args()

    def git(*argv):
        return subprocess.check_output(['git', '-C', str(args.bench), *argv], text=True)

    prefix = 'ShorECDLP/Submission/2607_13816/'
    files = [p for p in git('diff', '--name-only', '--diff-filter=A', args.base,
                            args.upstream, '--', prefix).splitlines() if p.endswith('.lean')]
    modules = {f'ShorECDLP.Submission.«2607_13816».{p[len(prefix):-5].replace("/", ".")}':
               f'ShorECDLP.Submission.Entrant.Streaming.{p[len(prefix):-5].replace("/", ".")}'
               for p in files}
    target = args.bench / 'ShorECDLP/Submission/Entrant/Streaming'
    for path in files:
        source = git('show', f'{args.upstream}:{path}')
        source = re.sub(r'(?m)^(import\s+)(\S+)',
                        lambda m: m[1] + modules.get(m[2], m[2]), source)
        dest = target / path[len(prefix):]
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(source)
    print(f'Ported {len(files)} Lean modules from {git("rev-parse", args.upstream).strip()}')
    if args.rounds == 26:
        reduce_rounds(target)
        print('Applied 26-round adaptation and added Challenge/Rounds.lean')


if __name__ == '__main__':
    main()
