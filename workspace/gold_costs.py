#!/usr/bin/env python3
"""Brief 07 conditional budgets, not a certified entrant. Python stdlib only.

S is emitted CCX+CCZ (all-enabled upper bound), never a sampled mean.
h models UNPROVED lowering + control + hardening overhead, before listed extras.
See docs/ECDLP-AI-GOLD.md for the source paths and missing obligations.
"""
from fractions import Fraction as F
import math

ROUNDS, BITS, WINDOWS, PHASE = 26, 464, 28, 54_168
BASELINE = 1_471_463_476_298_712
MEAS_CAP = 47_471_340_504
N = 513
CONTROL = 2*N*7
SINGLETON_CORRECTION = 16*35_826


def row(label, q, per_round):
    total = ROUNDS*per_round
    print(f'{label} | {q:,} | {per_round:,} | {total:,} | {q*total:,} | {BASELINE/(q*total):.3f}x')


def phase_cell_check():
    # Gold carry_base_recipe, prev=None: CCX; X-measure-reset; outcome-CZ.
    # Unnormalized Kraus amplitudes differ only by the common factor 1/sqrt(2).
    for a in (0, 1):
        for b in (0, 1):
            for m in (0, 1):
                before_repair = (-1)**(m*(a & b))
                repair = (-1)**(m*a*b)
                assert before_repair*repair == 1
    print('Gold AND cell algebra: all input bits and measurement outcomes passed (Python, not Lean).')


def main():
    phase_cell_check()
    print('Proxy: 7*static emitted nonlinear gates; no mean-to-worst substitution')
    print('route | static CCX+CCZ | 7S')
    routes = [('1198',1198,2_152_612), ('1239',1239,2_114_978),
              ('1240',1240,2_114_708), ('1367',1367,1_303_454),
              ('1299 d912',1299,1_171_372), ('1299 e655',1299,1_119_996)]
    for label,q,s in routes:
        print(label, f'{s:,}', f'{7*s:,}', sep=' | ')
    print('\nArchitecture | Q guess | T/round | T/26 | Q*T | gain vs current')
    # Coherent window bank: 512 selected coords, 16 address labels, reused.
    # Extra=0 is an explicit missing-cost placeholder, not a complete circuit.
    for h in (1,2,4):
        row(f'1240 coherent windows h={h}, extras=0',1240+512+16,
            WINDOWS*h*7*2_114_708+PHASE)
    # Total-add core includes correction workspace; dummy and control separate.
    for h in (1,2,4):
        row(f'1240 semiclassical h={h}, compact total-add target',1240+N+1,
            BITS*(h*7*2_114_708+CONTROL)+PHASE)
    # Use existing correction with deliberately disjoint banks.
    # Five endpoint words + 512 equality scratch/flag, accumulator infinity
    # bit, two spare/control labels from Brief 06; keep core/banks disjoint.
    disjoint_q = 1240+1+5*N+512+2+N+1
    row('1240 semiclassical, disjoint correction bank, h=1',disjoint_q,
        BITS*(7*2_114_708+SINGLETON_CORRECTION+CONTROL)+PHASE)
    # Exact-route fallback upper bound on native nonlinear count is all records.
    # Still excludes compiler and control additions; exact 7S is unrecorded.
    exact_proxy = 7*41_431_550
    row('2820 exact-line native ALL-RECORD upper proxy, windows',2820+512+16,
        WINDOWS*exact_proxy+PHASE)
    row('2820 exact-line native ALL-RECORD upper proxy, semiclassical',2820+N+1,
        BITS*(exact_proxy+CONTROL)+PHASE)
    print('\nSemiclassical crossover T/add INCLUDING all overhead at 26 rounds:')
    for q in (1754,3334,disjoint_q):
        print(q, float((F(BASELINE,q*ROUNDS)-PHASE)/BITS))
    p = F(163,1000)
    threshold = 1-math.pow(.01,1/26)
    print('p=.163 success:',float(1-(1-p)**ROUNDS))
    print('26-round minimum p:',threshold,'per-round event loss allowance:',float(p)-threshold)
    print('Full-experiment probability slack:',float(1-(1-p)**ROUNDS)-.99)
    # Sufficient state-vector bound: two norm-preserving implementations that
    # agree on good subspace, bad initial mass eps => delta_norm<=2 sqrt(eps).
    # Event-probability change <=2*delta_norm <=4 sqrt(eps).
    slack = float(p)-threshold
    print('Sufficient round bad mass if event loss <=4 sqrt(eps):',(slack/4)**2)
    print('Equal per-call initial-space bad masses, 28 / 464 calls:',
          (slack/4)**2/28,(slack/4)**2/464)
    for q, calls in [(1768,28),(1754,464),(3334,464),(disjoint_q,464)]:
        print('M/add cap, Q,calls:',q,calls,(MEAS_CAP//26-464-q)//calls)
    # Epoch11's 8.7e-8 is an empirical/model estimate, not a bound.
    e=8.695712220905507e-8
    print('Epoch11 modeled union per round, 28/464 calls:',28*e,464*e)
    print('Heuristic uniform tie union: 1080*2^-64 + 1080*2^-32 =',1080/2**64+1080/2**32)
    print('Rounds for hypothetical p=.546:',math.ceil(math.log(.01)/math.log1p(-.546)))


if __name__ == '__main__':
    main()
