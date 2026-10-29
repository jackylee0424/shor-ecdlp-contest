"""Survey arithmetic only; none of these estimates is a Lean resource proof.

Sources and assumptions are documented in docs/RELATED-WORK.md.
"""
from fractions import Fraction

CCX_T = 7
TRIALS = 56
WINDOW_ADDS = 28
QFT_PHASES_PER_TRIAL = 54168

def main():
    paper_t = 800_005_504_760
    print("paper legacy Q*T:", 854 * paper_t)
    c77_static = 2_425_952  # CCX + CCZ, POSTPASS_CTX final
    c77_t = CCX_T * c77_static
    print("C77 static all-enabled T/add:", c77_t)
    print("C77 867-qubit T-product/add:", 867 * c77_t)
    print("C77 sampled-mean conversion (NOT a bound):", 7 * Fraction('2244389.598'))
    for adds in [WINDOW_ADDS, 464]:
        t = TRIALS * (adds * c77_t + QFT_PHASES_PER_TRIAL)
        print(f"C77 {adds} adds/trial, 56 trials, excluding lookup/control/repair:", t)
        print("  hypothetical 883-wire Q*T:", 883 * t)
    print("full-width 256-bit MBU carry chain T:", 7 * (256 - 1))
    print("rot8 Fredkin T:", 509 * 7)
    print("cmod_barrel8 pilot repriced T:", 615 * 7)
    print("C74 branch-weight component proxies (NOT bounds):")
    for name, value in [('forward walk', 619333), ('inverse walk', 980483),
                        ('shell', Fraction('644605.5')), ('square class', 58675)]:
        print(" ", name, value * 7)

if __name__ == '__main__':
    main()
