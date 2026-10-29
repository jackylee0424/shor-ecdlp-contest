"""Exact round arithmetic, without floating point in the success test."""
from fractions import Fraction

per_round_t = 806028979896 // 56
per_round_m = 48194018992 // 56
assert per_round_t * 56 == 806028979896
assert per_round_m * 56 == 48194018992
for rounds in (25, 26, 56):
    success = 1 - Fraction(837, 1000) ** rounds
    print(f'{rounds=}: T={rounds * per_round_t}, measurements={rounds * per_round_m}, '
          f'Q*T={3932 * rounds * per_round_t}, success={float(success):.12f}, '
          f'meets99={success >= Fraction(99, 100)}')
assert 1 - Fraction(837, 1000) ** 25 < Fraction(99, 100)
assert 1 - Fraction(837, 1000) ** 26 >= Fraction(99, 100)
