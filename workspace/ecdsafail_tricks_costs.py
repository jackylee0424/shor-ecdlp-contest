#!/usr/bin/env python3
"""Brief 06: source-labelled arithmetic, not a circuit resource certificate.

Run from any directory. No third-party packages, bench writes or Lean execution.
Archived means are printed separately from conditional static/worst-case budgets.
Source references and qualifications: docs/ECDSAFAIL-TRICKS.md.
"""
from fractions import Fraction
from pathlib import Path
import json
import math
import re

LAB = Path(__file__).resolve().parents[1]
IDS = """01a5cc2 3493c83 8e9c9a2 6c0e30c 92214c2 b87bdf7 6af22f9
dc0f02e 9a8bbca a3f9f6a 6b478c8 55edbc4 31abffd 0ab84d9 39a9153
f95b5d9 f0bd623 8d916b4 8cbf348 e35d2d1 366ef54 9fc252c 1994d6a da2b459""".split()
T_ROUND, ROUNDS, BITS, PHASE = 14_393_374_641, 26, 464, 54_168
PORT = 3932 * ROUNDS * T_ROUND
FRONTIER = 7_243_285_108_034_080_000
CAP_M = 47_471_340_504
EEA = 28 * 4 * 15_910_015 * 7
N = 513  # x, y and infinity
CONTROL_T = 2 * N * 7  # two Fredkin layers; constant clears are Clifford
BATCH_CORRECTION = 16 * 35_826  # singleton-row BatchCost: nodes=0
C77_STATIC = 2_425_952 * 7  # archived static CCX+CCZ, NOT an exact kernel


def archived_rows():
    rows = {}
    for line in (LAB / 'research/ecdsafail-notes/submissions-2026-10-29.txt').read_text().splitlines():
        if line.split()[0] not in IDS:
            continue
        match = re.search(r'^(\w+)\s+\S+\s+(\w+)\s+(\d+)\s+(\{[^}]+\})', line)
        assert match, line
        ident, status, score, data = match.groups()
        data = json.loads(data)
        assert int(score) == data['qubits'] * data['toffoli'], ident
        rows[ident] = (status, data['qubits'], data['toffoli'])
    assert set(rows) == set(IDS)
    return rows


def reflection_check(n=258):
    """Check the claimed permutation on every index and all eight controls."""
    swaps = [sum(i < (axis-i) % n for i in range(n)) for axis in (1, 0, -2, -6)]
    assert swaps == [129, 128, 128, 128]
    for shift in range(8):
        a, b, c = [(shift >> j) & 1 for j in range(3)]
        for i in range(n):
            pos = i
            for axis, control in zip((1, 0, -2, -6), (a, a ^ b, b ^ c, c)):
                if control:
                    pos = (axis-pos) % n
            # The note uses reversed physical lane order.
            assert pos == (i-shift) % n
    return sum(swaps)


def affine_check():
    """Exhaust the five-wire reversible identity in note 6af22f9."""
    # a,b=controls; c=bridge; d=temp; e=output
    left = [(0, 1, 3), (3, 4), (3, 2), (3, 4), (2, 4), (3, 2), (0, 1, 3)]
    right = [(2, 4), (3, 4), (0, 1, 4)]
    def run(word, gates):
        for gate in gates:
            if all((word >> q) & 1 for q in gate[:-1]):
                word ^= 1 << gate[-1]
        return word
    assert all(run(word, left) == run(word, right) for word in range(32))


def controlled_translation_check():
    """Toy cyclic-group check of dummy-point control including dummy cleanup."""
    for order in (7, 11):
        for offset in range(order):
            for value in range(order):
                for control in (0, 1):
                    a, dummy = value, 0
                    if control:
                        a, dummy = dummy, a
                    dummy = (dummy+offset) % order
                    if control:
                        a, dummy = dummy, a
                    # Real encoding clears known offset by bitwise XOR when c=0.
                    if not control:
                        dummy ^= offset
                    assert (a, dummy) == ((value+control*offset) % order, 0)


def dirty_mcx_check():
    """Exhaust dirty-chain action AND donor restoration at k=3..6.

    Transcribed from lowq-lineage/bk666/src/point_add/mask.rs::mcx_dirty.
    This is discovery validation, not a Lean proof for arbitrary k.
    """
    for k in range(3, 7):
        target = k
        dirty = list(range(k+1, 2*k-1))
        gates = []
        for _ in range(2):
            gates.append((k-1, dirty[k-3], target))
            for i in reversed(range(1, k-2)):
                gates.append((i+1, dirty[i-1], dirty[i]))
            gates.append((0, 1, dirty[0]))
            for i in range(1, k-2):
                gates.append((i+1, dirty[i-1], dirty[i]))
        assert len(gates) == 4*(k-2)
        for word in range(1 << (2*k-1)):
            out = word
            for a, b, t in gates:
                if (out >> a) & (out >> b) & 1:
                    out ^= 1 << t
            expected = word ^ ((1 << target) if word & ((1 << k)-1) == (1 << k)-1 else 0)
            assert out == expected


def main():
    rows = archived_rows()
    print('ARCHIVED metrics: status | qubits | MEAN Toffoli (not worst-case T)')
    for ident in IDS:
        print(ident, *rows[ident], sep=' | ')
    affine_check()
    controlled_translation_check()
    dirty_mcx_check()
    print('\nSmall algebra checks passed: affine identity; dummy-point control; reflections', reflection_check())
    print('PORT Q*T:', PORT, 'FRONTIER:', FRONTIER)
    print('EEA T/round:', EEA, 'fraction:', EEA/T_ROUND)
    print('10%,25% EEA removal savings:', EEA//10, EEA//4, '(integer floors)')
    print('Controlled-add swap overhead:', CONTROL_T)
    print('Singleton batch correction T:', BATCH_CORRECTION)
    print('C77 static old-stream proxy:', C77_STATIC)
    dirty_compare_delta = 16*4*7*(4*(513-2)-(2*513-3))
    assert dirty_compare_delta == 457_408
    dirty_round = T_ROUND+28*dirty_compare_delta
    print('\nExact-dirty-comparator design (pending Lean):')
    for q in (3421, 3111):
        score = q*26*dirty_round
        print('Q, T/round, T/26, score, port gain:', q, dirty_round, 26*dirty_round, score, PORT/score)
    print('r=26 success with p=.163:', 1-Fraction(837, 1000)**26)
    print('r=26 decimal:', float(1-Fraction(837, 1000)**26))
    print('\nConditional all-input exact core budgets: tabulated Q includes wrapper and correction workspace')
    print('label | Q | T/add | T/round | T/26 | Q*T | improvement vs port | vs frontier')
    scenarios = [
        # Retain proved paper arithmetic, specialize both query trees to one leaf.
        # This is a source-derived budget for a new compiler, not an instantiated certificate.
        ('Protected arithmetic singleton design; existing support bound', 3932+N+1,
         514_030_776-10*(2**15-1)*7-14*(2**15-1)*7+CONTROL_T),
        # No row is a proved exact point-add bound. h is a hardening multiplier.
        ('C77 h=1 + existing singleton correction; disjoint banks', 4106, C77_STATIC+BATCH_CORRECTION+CONTROL_T),
        ('C77 h=2 + existing singleton correction; disjoint banks', 4106, 2*C77_STATIC+BATCH_CORRECTION+CONTROL_T),
        ('compact exact total-add target: 1024 wires, 30M T', 1024+N+1, 30_000_000+CONTROL_T),
        ('compact exact total-add target: 1286 wires, 100M T', 1286+N+1, 100_000_000+CONTROL_T),
    ]
    for label, q, per_add in scenarios:
        per_round = BITS*per_add+PHASE
        total = ROUNDS*per_round
        score = q*total
        print(label, q, per_add, per_round, total, score, f'{PORT/score:.5f}', f'{FRONTIER/score:.2f}', sep=' | ')
    print('\nT/add crossover for beating port at 26 rounds (includes control+exceptions):')
    for q in (870, 1200, 1538, 1800, 4106):
        threshold = (Fraction(PORT, q*ROUNDS)-PHASE)/BITS
        print(q, float(threshold))
    print('Maximum measurements/add at 26 rounds, allowing 464 Fourier+4106 resets/round:',
          (CAP_M//26-464-4106)//BITS)
    for p in (.163, .546):
        rounds_needed = math.ceil(math.log(.01)/math.log1p(-p))
        print('p, rounds:', p, rounds_needed)
    print('Reflection gross Toffoli saving/add, 254/260 slots:', 256*254*4, 256*260*4)
    print('MCX clean-bank saving/call:', 'k-2 scratch; 4(k-2) -> 2k-3; delta=2k-5 CCX')
    print('Note 55edbc4 static bank saving:', (490_229_937-427_625_727)*7, 'T/add old stream')
    print('Worst-case error union budget if all 12064 calls charged equally:', .0002/(26*464))


if __name__ == '__main__':
    main()
