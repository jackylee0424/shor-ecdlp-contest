"""Screen generalizations of the WEX leader (f1518daf, 674,031,241,128).

All figures are projections from public notes; nothing here is proved.
T = 4*(first_load + adds*body_ccx) + fourier + 1   (4-P lowering, Y catalyst)
"""
ADDS, FIRST, FOURIER = 29, 65_535, 56_773
TRAV = 32_767                      # one 15-bit unary traversal
ARITH_WEX = 2_216_363              # c3f340a ECDSAAdd arithmetic CCX / addition
NEG = 2_044                        # two outer Y negations
Q_WEX, Q_ADDER_WEX = 1_932, 1_899  # WEX total; Skywalk/c3f340a adder qubits (ioWires incl.)
LEADER = 674_031_241_128

def T(body): return 4 * (FIRST + ADDS * body) + FOURIER + 1
def score(q, body): return q * T(body)
def row(name, q, arith, trav, extra=0):
    body = arith + trav * TRAV + NEG + extra
    s = score(q, body)
    print(f"{name:58s} Q={q:5d} body={body:9,d} T={T(body):13,d} QxT={s:19,d} {100*(s/LEADER-1):+7.2f}%")
    return s

assert score(Q_WEX, ARITH_WEX + 24 * TRAV + NEG) == LEADER
row("leader f1518daf (24 traversals)", Q_WEX, ARITH_WEX, 24)
# L1: swap in the current ecdsafail-lean leader adder (0b650bb): 1,594 Q x 2,155,232 Toffoli
for dq in (0, 8, 32):
    row(f"L1 adder swap 0b650bb, overhead +{dq} wires", Q_WEX - (Q_ADDER_WEX - 1_594) + dq, 2_155_232, 24)
q1 = Q_WEX - (Q_ADDER_WEX - 1_594)
# L2: traversal fusion (merge loads whose targets are idle together)
for n in (20, 16, 12):
    row(f"L1 + L2 fuse to {n} traversals", q1, 2_155_232, n)
# L3: measured unlookup: each compute/uncompute pair pays one full traversal + ~sqrt-split unload
# unload ~ 2*2^8 CCX using 2^7..2^8 borrowed clean wires (0 Q if adder workspace is idle then)
for pairs, dq in ((8, 0), (8, 128), (12, 0)):
    s = row(f"L1 + L3 {pairs} unloads measured (+{dq} Q)", q1 + dq, 2_155_232, 24 - pairs, extra=pairs * 2 * 256)
