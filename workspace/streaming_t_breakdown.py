#!/usr/bin/env python3
"""Brief 05 exact upstream resource formulas and conditional lever accounting.

Sources: b46e337 Challenge/{WindowCounts,BatchCost,UniformT},
Window/LookupPrimitiveCounts, Arithmetic/InPlacePrimitiveCounts.
No benchmark execution or certificate claim; all prospective changes conditional.
"""
from collections import OrderedDict

ROUNDS, WINDOWS, Q = 26, 28, 3932
T_ROUND = 14_393_374_641
NEGATE = 3062*7
components = OrderedDict([
    ('EEA forward/reverse wrappers (4 per window)', 4*15_910_015*7),
    ('Horner multiply/unmultiply (6 per window)', 6*1_110_533*7),
    ('Zero-allowed wrappers (2 pairs per window)', 2*1018*7),
    ('Square/subtract', 2_223_879*7),
    ('Coordinate QROM traversals (10 per window)', 10*(2**15-1)*7),
    ('Coordinate modular lookup adders (5 per window)', 5*2813*7),
    ('Coordinate negations (4 signed + 1 x)', 5*NEGATE),
    ('Outer sign negations (2 per window)', 2*NEGATE),
    ('Correction queries (14 per window)', 14*(2**15-1)*7),
    ('Correction transpositions (16 per window)', 16*35_826),
])
assert sum(components.values()) == 514_030_776
assert sum(list(components.values())[:7]) == 510_203_526
round_components = {k: WINDOWS*v for k, v in components.items()}
round_components['First 16-bit point QROM'] = (2**16-1)*7
round_components['Fourier feedback (upper bound)'] = 256*255//2+208*207//2
assert sum(round_components.values()) == T_ROUND
assert ROUNDS*T_ROUND == 374_227_740_666

# Explicit allocation and a correction-only bijective relocation.
reset = list(range(837))+[838]+list(range(855, 871))
old = set(reset)|{837}
endpoint = set(range(1024, 3589))
comparator = set(range(4102, 4614))
assert len(old) == 855
assert len(old | endpoint | comparator) == 3932
data = set(range(263, 519))|set(range(580, 836))|{838}
bank = set(range(855, 871))
control_path = {836}|set(range(519, 534))
loan = sorted(old-data-bank-control_path)
assert len(loan) == 310
fresh = sorted(endpoint|comparator)
swaps = dict(zip(fresh, loan))
swaps.update({v: k for k, v in list(swaps.items())})
perm = lambda w: swaps.get(w, w)
correction_support = data|bank|control_path|endpoint|comparator
compact = old|{perm(w) for w in correction_support}
assert len(compact) == 3622
assert all(perm(perm(w)) == w for w in old|endpoint|comparator)

if __name__ == '__main__':
    print('Component | T/window | T/round | percent of round')
    for name, value in round_components.items():
        print(f'{name} | {components.get(name, "-")} | {value} | {100*value/T_ROUND:.6f}%')
    print('TOTAL/round:', T_ROUND, 'TOTAL/26:', ROUNDS*T_ROUND)
    print('\nSupport: original', len(old), '+endpoint', len(endpoint), '+comparator', len(comparator))
    print('Correction-only loans:', len(loan), '=>', len(compact), 'global labels')
    for wires in (3932, 3622, 3607, 3606, 870, 855):
        print('Q', wires, 'score', wires*ROUNDS*T_ROUND,
              'improvement factor', Q/wires)
    print('\nConditional savings: label | T/round saved | percent | T/26 saved')
    savings = {
        'Cancel adjacent two measured sign-negations': WINDOWS*2*NEGATE,
        'Make 64 comparisons/window use measured carry cleanup': WINDOWS*64*511*7,
        '10% of EEA wrapper T removed': round_components[next(iter(components))]/10,
        '25% of EEA wrapper T removed': round_components[next(iter(components))]/4,
        'Remove ALL correction cost (ceiling, not achievable claim)': WINDOWS*3_784_382,
    }
    for name, val in savings.items():
        print(f'{name} | {val} | {100*val/T_ROUND:.6f}% | {ROUNDS*val}')
    print('6 rounds, 3622 wires:', 6*T_ROUND, 'T;', 3622*6*T_ROUND, 'Q*T')
    print('near-870 crossover T/window:', (Q/870*T_ROUND-458745-54168)/WINDOWS)
    print('Naive row-stream correction proxy:', 32768*16*4*(2*529-3)*7, 'T/window')
