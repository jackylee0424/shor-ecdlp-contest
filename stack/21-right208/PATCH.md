# Patch 21 — one fewer right window (parked)

Owner: Brief 15. Priced on dadon bench `c13a293` plus enabled patch 20,
2026-10-29. This directory intentionally has no `ENABLED` file.

## Verdict

The requested 208-bit physical right axis does **not** clear 99% success. A
13-window, 208-bit register has only 32 fine outcomes per decoded 203-bit bin.
The large-order finite-kernel limit gives averaged right mass
`0.971734399447`; composing with the leader's left `200/201` bound gives only
`0.966899899947`. This is substantially below 0.99, so no Entrant mutation was
made.

There is also a conservative finite-order rejection bound, independent of the
limiting integral. Multiplication by `2^203` permutes residues modulo the odd
prime order. In four disjoint residue strips immediately below the positive
coarse-bin boundary, one fine outcome lies outside the accepted bin at phase
distances in `[0,1/4]`, `[1/4,1/2]`, `[1/2,3/4]`, and `[3/4,7/8]`.
The exact finite QPE kernel dominates sinc² at the same distance. Using the
rational lower bounds `4/5`, `2/5`, `4/45`, and `9/490`, and charging one
residue of floor loss per strip, forces average failure at least

`11449/1128960 - 1153/(882*order)`.

Thus the finite right mass is below `0.989858808107` (the displayed decimal
already safely ignores a <`2/order` correction), and even this deliberately
loose upper bound composes with `200/201` to below `0.984934137420`. Therefore
the direct 208-bit design is rigorously separated from 99%; the tighter sinc
integral is used only to rank the alternatives.

The leader's existing inverse-square theorem cannot repair this: its
concentration interval is centered on the exact fine-register phase, while the
accepted 32-outcome bin is centered on the rounded 203-bit phase and can put
the exact phase at a bin boundary. A pointwise radius-16 tail estimate therefore
does not imply the required coarse-bin event.

## Re-split pricing

Bits 209–211 require respectively one, two, or three specialized 17-bit
windows among the thirteen right windows, plus a seventeenth address wire.
Using the exact conditional 17-bit cost `515,139,247 T` after cancellation:

| Physical right bits | Limiting right mass | With left `200/201` | Rows | Q | Conditional T | Status |
|---:|---:|---:|---:|---:|---:|---|
| 208 | 0.971734399447 | 0.966899899947 | 868,352 | 855 | 14,839,659,641 | fails success |
| 209 | 0.984769781038 | 0.979870428893 | 901,120 | 856 | 14,842,641,737 | fails success |
| 210 | 0.991836206356 | 0.986901697867 | 933,888 | 856 | 14,845,623,834 | fails success |
| 211 | 0.995643764012 | 0.990690312450 | 966,656 | 856 | 14,848,605,932 | numerically plausible, unproved |
| 212 | 0.997684710906 | 0.992721105379 | 999,424 | 856 | 14,851,588,031 | exceeds row cap |

The integer resources are exact conditional on a width-17 physical tree. The
mass figures are deterministic sinc-kernel integrals and are not finite-order
Lean theorems. Thus 211 bits is a real future proof target, but it does not meet
this brief's “exact numbers clear 0.99” gate today: it needs a new averaged
coarse-bin finite-kernel theorem, three width-17 tree implementations, and a
proved clean/reused seventeenth bank wire (otherwise Q=856 as priced).

Trimming the left axis 263→262 converts one 16-bit left window to 15 bits and
frees exactly 16,384 rows. Consequently the 212-bit option fits at exactly
983,040 rows and conditionally costs 14,850,096,825 T at 856 qubits
(Q×T 12,711,682,882,200). Its averaged limiting union bound is about
`0.996833869611 + 0.997684710906 - 1 = 0.994518580517`, but both the 262-bit
left average and the 212→203 coarse-bin average lack the required finite Lean
proof. This option is also parked.

Reproduce all figures with `src/right-window-pricing.py` or the extended
`workspace/fewer_windows.py`. `apply.sh` exits 3 without editing the bench.
