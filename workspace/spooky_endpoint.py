#!/usr/bin/env python3
"""Spooky pebbling vs. the batched endpoint correction (brief 09 follow-up).

Pure standard-library calculator. Run: python3 workspace/spooky_endpoint.py
All upstream constants are copied from the pinned upstream sources
(Challenge/BatchCost.lean, BatchedEndpoint.lean, WindowBody.lean) and the
lab's accepted six-round entrant; everything labelled DESIGN/GUESS is a
prediction, not a certified count.

Sections
  1. Upstream correction: per-window T, queries, swaps, word lifetimes.
  2. Pebbling search: minimum number of simultaneously resident 513-bit
     endpoint words for the upstream conjugation algorithm when words may be
     freely X-measured (spooky) and recomputed.  Result: 5 (no saving).
  3. Spooky variant priced (zero Q gain, extra T).
  4. Flag-only "in-place table comparison" correction (no resident words),
     the alternative the analysis uncovered.  Q, T, measurements, Q x T.
"""
from collections import deque
from itertools import combinations

# ---------------------------------------------------------------- constants
NODES = 32767                      # batchWindowTree.internalNodes (32768 leaves)
QUERY_T = 7 * NODES                # batchQuery_tCount: 229,369 T, leaf T = 0
QUERY_MEAS = NODES                 # lookupMeasurements per query
EQ_CLEAN_CCX = 2 * 513 - 3         # mcxVChainToffoliCost 513 = 1023
EQ_DIRTY_CCX = 4 * (513 - 2)       # dirty chain (brief 09) = 2044
SWAP_T = 35826                     # batchOpCircuit_tCount (4 eq tests + update)
UPDATE_T = SWAP_T - 4 * 7 * EQ_CLEAN_CCX  # 7,182 T = 1,026 CCX word update
WINDOW_T = 3784382                 # placedBatchSource_tCount
ROUND_T = 14_393_374_641           # accepted six-round entrant, per round
ROUNDS = 6
ADD_WINDOWS = 28                   # batched windows per round (15 left + 13 right)
MEAS_TOTAL = 5_163_644_892         # accepted entrant, all rounds
MEAS_CAP = 47_471_340_504
Q_BASE, Q_09 = 3932, 3111
CORE_Q = 855                       # 0-836, 837, 838, 855-870 (CONTRIBUTIONS-PLAN 1)
FREE_AT_CORRECTION = 310           # clean arithmetic labels at the correction boundary

SCHEDULE = [("q", True, 3), ("s", 3, 2), ("s", 3, 1), ("s", 3, 0), ("s", 3, 5), ("q", False, 3),
            ("q", False, 2), ("s", 2, 1), ("s", 2, 0), ("s", 2, 5), ("q", False, 2),
            ("q", False, 1), ("s", 1, 0), ("s", 1, 5), ("q", False, 1),
            ("q", False, 0), ("s", 0, 5), ("q", False, 0),
            ("q", False, 1), ("s", 1, 0), ("q", False, 1),
            ("q", False, 2), ("s", 2, 0), ("s", 2, 1), ("q", False, 2),
            ("q", False, 3), ("s", 3, 0), ("s", 3, 1), ("s", 3, 2), ("q", True, 3)]


def section1():
    nq = sum(op[0] == "q" for op in SCHEDULE)
    ns = sum(op[0] == "s" for op in SCHEDULE)
    assert (nq, ns) == (14, 16)
    assert nq * QUERY_T + ns * SWAP_T == WINDOW_T
    assert UPDATE_T == 7182
    print("1. upstream batched correction (per addition window)")
    print(f"   queries {nq} x {QUERY_T:,} T = {nq*QUERY_T:,};  swaps {ns} x {SWAP_T:,} T = {ns*SWAP_T:,}")
    print(f"   window T {WINDOW_T:,} = {100*WINDOW_T*ADD_WINDOWS/ROUND_T:.3f}% of a round")
    # lifetimes: which op indices read / write each word
    uses = {w: [] for w in range(6)}
    for i, op in enumerate(SCHEDULE):
        if op[0] == "s":
            _, a, t = op
            uses[a].append((i, "a")); uses[4].append((i, "b")); uses[t].append((i, "W"))
        else:
            _, src, k = op
            uses[4].append((i, f"xor t{k}"))
            if src:
                for w in range(4):
                    uses[w].append((i, "xor s"))
    for w in range(5):
        print(f"   W{w}: " + " ".join(f"{i}{r}" for i, r in uses[w]))
    fwd_q = sum(op[0] == "q" for op in SCHEDULE[:18]); fwd_s = sum(op[0] == "s" for op in SCHEDULE[:18])
    print(f"   forward half ops 0-17: {fwd_q} queries, {fwd_s} swaps;"
          f" backward half ops 18-29: {nq-fwd_q} queries, {ns-fwd_s} swaps")
    # dirty comparator delta (brief 09)
    d_swap = 4 * (EQ_DIRTY_CCX - EQ_CLEAN_CCX) * 7
    assert d_swap == 28588
    print(f"   brief 09 dirty comparator: +{d_swap:,} T/swap, +{16*d_swap*ADD_WINDOWS:,} T/round")
    return d_swap


# ------------------------------------------------------------ pebbling search
# Register contents: ('t',k) raw target column; ('x',j,d) source column s_j
# after d conjugators (tau'_3, tau'_2, ...) have been applied; u_j = ('x',j,3-j).
# Moves: load a raw column into a free register; free any register (spooky
# X-measure, repair cost ignored -> this is a LOWER bound); apply tau'_k
# (needs u_k and t_k resident) to a source register whose next conjugator is k
# or to the accumulator whose next step is k.  Accumulator order 3,2,1,0.

def min_resident_words(max_words=6):
    def moves(state, acc):
        regs = list(state)
        out = []
        # load raw column
        if len(regs) < cap:
            for k in range(4):
                out.append((tuple(sorted(regs + [("t", k)])), acc))
                out.append((tuple(sorted(regs + [("x", k, 0)])), acc))
        # free (spooky measure) any register
        for i in range(len(regs)):
            out.append((tuple(sorted(regs[:i] + regs[i+1:])), acc))
        # transpositions
        for k in range(4):
            uk = ("x", k, 3 - k)
            if uk in regs and ("t", k) in regs:
                if acc < 4 and 3 - acc == k:
                    out.append((state, acc + 1))
                for i, r in enumerate(regs):
                    if r[0] == "x" and r != uk and r[1] < k and 3 - r[2] == k:
                        nr = regs[:i] + [("x", r[1], r[2] + 1)] + regs[i+1:]
                        out.append((tuple(sorted(nr)), acc))
        return out
    for cap in range(1, max_words + 1):
        start = ((), 0)
        seen = {start}
        dq = deque([start])
        while dq:
            st, acc = dq.popleft()
            if acc == 4:
                return cap
            for nxt in moves(st, acc):
                if nxt not in seen:
                    seen.add(nxt); dq.append(nxt)
    return None


def section2():
    m = min_resident_words()
    print("2. pebbling lower bound (upstream conjugation algorithm, free spooky discard/recompute)")
    print(f"   minimum simultaneously resident endpoint words = {m}  (upstream uses 5)")
    assert m == 5
    return m


def section3(d_swap):
    # Best spooky schedule found by hand: X-measure W3 after op 4 and reload it
    # inside the existing op-25 query (raw column s3: reload/unload are free in
    # shared queries, so spooky is never better than coherent folding there);
    # conjugated words W0..W2 hold u_j(row), whose phase (-1)^{m.u_j(row)} is a
    # non-linear function of table constants -> not expressible as whenBit
    # leaf gates; repair = recompute u_j = replay forward conjugation.
    print("3. spooky on the endpoint bank, priced")
    print("   peak words unchanged at 5 (section 2) -> qubits unchanged: brief 09 stays 3,111")
    swap09 = SWAP_T + d_swap
    # cheapest recompute of each conjugated word = its forward conjugating swaps
    recompute_swaps = {2: 1, 1: 2, 0: 3}   # tau'_3 (and tau'_2, tau'_1) applications
    recompute_queries = {2: 2, 1: 4, 0: 6}  # load/unload the t_k columns used (lower estimate)
    extra = sum(recompute_swaps[j]*swap09 + recompute_queries[j]*QUERY_T for j in recompute_swaps)
    print(f"   eliminating the backward half by measuring W0..W2 would need ~{extra:,} T/window of"
          " recomputation for phase repair, versus the backward half's"
          f" {6*QUERY_T + 6*swap09:,} T -> no T gain either")
    return extra


# --------------------------------------------- flag-only in-place correction
def section4(test_ccx=1300, queries=13, label="DESIGN"):
    """One-hot flags f_k = [acc == s_k(row)] computed by XORing the table
    column into the accumulator with an ordinary query (leaf CX gates, 0 T),
    a 513-bit zero test into f_k, and chained column-difference queries.
    Update: four f_k-controlled queries XOR (s_k ^ t_k)(row) into acc.
    Clear: same chain with t_k columns.  No resident endpoint word."""
    tests = 8
    win_t = queries * QUERY_T + tests * 7 * test_ccx
    d_round = ADD_WINDOWS * (win_t - WINDOW_T)
    round_t = ROUND_T + d_round
    total_t = ROUNDS * round_t
    q = CORE_Q
    meas_win = queries * QUERY_T // 7 + tests * 260          # ~260 AND erasures per test (GUESS)
    d_meas_round = ADD_WINDOWS * (meas_win - 14 * QUERY_MEAS) - (3931 - 854)  # reset list shrinks
    meas_total = MEAS_TOTAL + ROUNDS * d_meas_round
    return dict(label=label, test_ccx=test_ccx, queries=queries, win_t=win_t, d_round=d_round,
                round_t=round_t, total_t=total_t, q=q, qt=q*total_t, meas=meas_total)


def main():
    d_swap = section1()
    section2()
    section3(d_swap)
    t09 = ROUNDS * (ROUND_T + 16 * d_swap * ADD_WINDOWS)
    qt09 = Q_09 * t09
    qt_now = Q_BASE * ROUNDS * ROUND_T
    assert qt_now == 339_568_494_530_472
    print(f"   brief 09 projection: {Q_09:,} x {t09:,} = {qt09:,} ({qt09:.3e})")
    print("4. flag-only correction (no endpoint bank) -- DESIGN prediction, not certified")
    rows = [section4(),                                   # clean-temp half chain + dirty half
            section4(test_ccx=EQ_DIRTY_CCX + 4 * 255),     # pessimistic split dirty MCX
            section4(test_ccx=4 * 4 * 255),               # 4 half-size dirty MCX, 1 borrowed anc
            section4(queries=14),                          # no query merge across the update
            section4(queries=18, test_ccx=4080)]           # 5+5 uncontrolled + 4 ctrl + slack
    for r in rows:
        assert r["meas"] < MEAS_CAP
        print(f"   test={r['test_ccx']:>5} CCX, queries={r['queries']}: window T {r['win_t']:,}"
              f" (d/round {r['d_round']:+,}); Q {r['q']} x T {r['total_t']:,} = {r['qt']:.4e};"
              f" vs brief09 x{qt09/r['qt']:.2f}, vs live x{qt_now/r['qt']:.2f}; meas {r['meas']:,}")
    # qubit budget during correction
    live = 513 + 16 + 1 + 15
    assert CORE_Q - live == FREE_AT_CORRECTION
    need = 4 + 255 + 1
    print(f"   correction workspace: 4 flags + <=255 AND temps + 1 anc = {need} <= {FREE_AT_CORRECTION} free"
          " clean labels -> support stays at the 855-label core")


def paper_check():
    """Section 7 of docs/SPOOKY-ON-09.md: exact zero-test layout and records."""
    print("7. paper check: exact flag-only resources")
    # zero test on 513 controls: A = 257 acc wires via clean Gidney AND chain
    # (256 ANDs: 255 temps + anc, measured erase), then f ^= AND(B[256] + anc)
    # by the dirty chain with 255 donors taken from A's acc wires.
    a_ands = 257 - 1
    dirty = 4 * ((256 + 1) - 2)
    test_ccx = a_ands + dirty
    assert test_ccx == 1276
    clean_needed = a_ands + 4                  # temps+anc, 4 flags
    assert clean_needed <= FREE_AT_CORRECTION
    win_t = 13 * QUERY_T + 8 * 7 * test_ccx
    d_round_t = ADD_WINDOWS * (win_t - WINDOW_T)
    total_t = ROUNDS * (ROUND_T + d_round_t)
    meas_win = 13 * QUERY_MEAS + 8 * a_ands
    d_meas_win = meas_win - 14 * QUERY_MEAS
    reset_drop = 3931 - 855                    # batchedResetWires 3,931 -> core 855 (incl. 837)
    d_meas_round = ADD_WINDOWS * d_meas_win - reset_drop
    meas_total = MEAS_TOTAL + ROUNDS * d_meas_round
    assert meas_total < MEAS_CAP
    qt = CORE_Q * total_t
    print(f"   test {test_ccx} CCX ({a_ands} clean-AND + {dirty} dirty), clean labels used {clean_needed}/310")
    print(f"   window T {win_t:,} (was {WINDOW_T:,}); dT/round {d_round_t:+,}; total T {total_t:,}")
    print(f"   meas/window {meas_win:,} ({d_meas_win:+,}); d/round {d_meas_round:+,}; total {meas_total:,}"
          f" < cap {MEAS_CAP:,} ({100*meas_total/MEAS_CAP:.2f}%)")
    print(f"   Q x T = {CORE_Q} x {total_t:,} = {qt:,} ({qt:.4e})")
    return qt


if __name__ == "__main__":
    main()
    paper_check()
