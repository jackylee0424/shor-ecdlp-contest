"""Projection calculator for docs/ECDSAFAIL-855.md (design estimates, not certified counts).

Run: wsl.exe -d gitzard-formal -- python3 /mnt/c/code/shor-ecdlp-contest/workspace/ecdsa855_levers.py
"""
Q0 = 855
T0 = 86_239_836_030          # frontier ff1bf8d, 6 rounds
BASE = Q0 * T0
WINDOWS = 28 * 6             # addition windows over the whole circuit
EEA_WINDOW_T = 445_480_420   # 4 measured wrappers, exact (EEA-INVENTORY)
WRAPPER_CCX = 15_910_015
HORNER_CCX = 1_110_533       # secp256k1HornerMulInverse / SquareInverse gidneyToffoliCount


def proj(dT_window, q=Q0):
    t = T0 - dT_window * WINDOWS
    return t, q * t, q * t / BASE


def row(name, dT_window, q=Q0):
    t, s, r = proj(dT_window, q)
    print(f"{name:52s} dT/window {dT_window:>14,.0f}  dT/round {dT_window*28:>16,.0f}  "
          f"Q {q:4d}  T {t:>18,.0f}  QxT {s:.4e}  ratio {r:.3f}")


def mul_saving(perbit, calls):
    new = 256 * perbit + 2_000          # + final canonicalisation allowance
    return (HORNER_CCX - new) * 7 * calls


print("frontier QxT", f"{BASE:,}")
for pb in (600, 800, 1000):
    row(f"L1 signed-digit folded Horner, {pb} CCX/bit, 6 mult", mul_saving(pb, 6))
    row(f"L1+L2 same cell also for 2 square calls, {pb}", mul_saving(pb, 8))
row("L3 drop one square call (measure lambda away)", HORNER_CCX * 7)
for slots in (405, 470, 560):
    new = 2 * slots * 18_250 * 7
    row(f"L4 greedyfrog-shaped exact EEA, {slots} slots", EEA_WINDOW_T - new)
for walk, q in ((0.5e6, 900), (0.7e6, 900), (0.7e6, 1030), (1.0e6, 1290)):
    row(f"L5 exact BY divstep walk {walk/1e6:.1f}M CCX/walk", EEA_WINDOW_T - 4 * walk * 7, q)
row("L4(470)+L1/L2(800)", EEA_WINDOW_T - 2 * 470 * 18_250 * 7 + mul_saving(800, 8))
row("L5(0.7M,900)+L1/L2(800)", EEA_WINDOW_T - 4 * 0.7e6 * 7 + mul_saving(800, 8), 900)
row("brief-12 held-product Block-E (reference)", 181_440)
# Lilypad-G forward-walk arithmetic estimate from lilypad_g_sched.txt sums
sum_kv, sum_kc, ticks = 73_405, 79_014, 532
print("Lilypad-G walk core ~2*(sum kv+kc) =", 2 * (sum_kv + sum_kc), "CCX for", ticks, "ticks")
print("bench wrapper / Lilypad core:", WRAPPER_CCX / (2 * (sum_kv + sum_kc)))
