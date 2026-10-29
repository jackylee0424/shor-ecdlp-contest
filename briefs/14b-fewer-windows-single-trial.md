# Brief 14b — fewer windows in the single-trial design (read-only analysis; supersedes brief 14)

Read `AGENTS.md`, `docs/LEVERS.md`, `docs/CONTRIBUTIONS-PLAN.md` §2 (decoder/candidate-budget table) and the leader's note (below).

## New baseline (2026-10-29 15:00)

Leader **dadon `3e53f42`** (bench commit `8513c15`): **855 × 16,901,720,498 = 14,450,971,025,790**, reproduced locally
(`entrants/20261029-1524-frontier-3e53f42`). It is ArthurOstapenko's `8c5e543` **single trial** with 263/263-bit precision and the protected
**`nearestPair`** decoder (one candidate), plus a verified literal-cancellation pass in each EEA microstep. Structure: 1 direct 16-bit load + 33 corrected
signed-window additions. The left axis is 16 + 7·16 + 9·15 = 263 and the right axis 8·16 + 9·15 = 263. The table has 851,968 of 983,040 rows. Success comes from a sharp rounding-window lemma
(mass ≥ 200/201 per axis when 128·r ≤ 2^t, which holds at t = 263; adapted from `da06e7d`). Each addition window is ≈ 497–514M T (EEA ≈ 87 %), so **every window removed ≈ −2.9 % T**.
**Our submission bar is > 10 % below the leader: Q×T < 13,005,873,923,211, i.e. remove ≥ 4 windows (or the equivalent T).**

Leader source: the bench `~/shorecdlp-m` (read-only for you; the Entrant files are `Main.lean`, `Streaming/{Certificate,Resources,Semantics}.lean`).

## Levers to analyze (rank them with exact numbers)

1. **Asymmetric widths with `wrappedShift`.** The protected decoder `wrappedShift` (`ShorECDLP/Challenge/Decoder.lean`) checks up to `2·(order/2^rightBits + 2)`
   candidates per trial against a total budget of `56·(2^49+2)` ≈ 2^55.8. With **one** trial, how small can the right axis be (≈ 203–210 bits?), and what must the
   left axis be? Characterize **exactly which outputs `wrappedShift` accepts** (does it cover neighbouring bins? how does the shift enumerate the right-axis ambiguity?),
   compute the true single-trial success for the best (left, right) widths, and check whether ≥ 0.99 is reachable and provable uniformly in d. Count the windows saved.
2. **A sharper success lemma for `nearestPair`.** Can t drop below 263 per axis (e.g. a bound that gives ≥ 0.99 overall from 64·r ≤ 2^t or less)? Since windows are 15–16 bits,
   say how many bits must go before a window disappears, and whether re-packing window widths makes small bit savings count.
3. **Window width re-packing under the row cap.** Wider windows (17-bit uses 65,536 rows; 15-bit 16,384; 16-bit 32,768) cut the window count but cost rows
   (cap 983,040; used 851,968) and lookup T (small). Find the optimal width assignment per axis under the cap, for each decoder option above.
4. **Combinations** of 1–3, and the resulting window count, T, Q×T, and % vs the leader.

For each: exact or not, proof effort (S/M/L/XL), which leader lemmas carry over (`program_success`, the rounding-window lemma, `signedRow`,
resource facts), and risks.

## Constraints and output

Read-only on every checkout; Lean scratch only via `BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/Win*.lean`. No submissions or commits.
Write `docs/FEWER-WINDOWS.md` (verdict first: which combination clears −10 %, if any), `workspace/fewer_windows.py`, a LOG line, and new rows in `docs/LEVERS.md`.
