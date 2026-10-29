# What the ~855-qubit ecdsa.fail builds do for inversion, multiplication and squaring

Research note, 2026-10-29. This extends `docs/ECDSAFAIL-TRICKS.md`. It does not repeat that survey, and it does not duplicate brief 12
(`docs/EEA-INVENTORY.md`, the exact per-cell inventory of the bench EEA). Numbers marked *est.* are design estimates. They are not
certified counts. Projections come from `workspace/ecdsa855_levers.py` (run it with WSL `python3`).

## Verdict (5 lines)

1. The ~30× gap is mostly **inversion**. One bench EEA wrapper costs 15,910,015 CCX. A Lilypad-G divstep walk at 855 q has an arithmetic core of about 0.30M CCX. That is ~50× less, and the four walks plus the shell are ~2.4M mean Toffoli per point add.
2. None of the ~855q inversions is exact. Lilypad-G uses fewer divsteps than the proven bound (532 vs 590), sampled per-tick widths, a capped run log and terminal range cuts. greedyfrog uses sampled windows, a 28-lane decode and 21-row capacity. Their failure rate is about 0.2% or less per shot, and a nonce search picks a passing corpus.
3. **The nearest bankable lever is not in the EEA. It is the multiplier** (modp_ft). Replace each bit of the bench's bit-serial controlled modular add plus halve (4,344 CCX/bit) with an **uncontrolled signed-digit add and a merged pseudo-Mersenne fold**. Made exact, this costs *est.* 600–1,000 CCX/bit. Over the 6 Horner calls and 2 square calls that saves ~10% of T: **Q×T ≈ 6.6–6.7e13 at 855 q**. It is exact, effort L, and complementary to brief 12.
4. The big EEA prize needs an architecture change. Either (a) **normalise instead of locate**, i.e. greedyfrog-style top-normalised rings with the partner cofactor under a marker, which removes the B/E interval decoders, or (b) a **public-schedule Bernstein–Yang divstep walk**. Projected Q×T is ~2.5–3.0e13 for (a) and ~1.2–2.1e13 for (b). Each has one or more **unsolved exactness obstacles**, so both are XL research, not briefs.
5. **Mean-only tricks are worth 0 on the bench.** The bench counts T worst-case. Conditioned phase-repair blocks are therefore charged in full. Their "½ per nesting level" weighting gives ecdsa.fail rows 1–10% that the bench cannot claim.

## Ranked levers

ΔT is per round (28 windows). Q×T assumes 6 rounds and is set against 73,735,059,805,650. "Brief 12" marks overlap with its candidate list.

| # | Lever | Source entries | Exact? | ΔT/round | ΔQ | Projected Q×T | Effort | Overlap with brief 12 |
|---|---|---|---|---:|---:|---:|---|---|
| L1 | Signed-digit **uncontrolled** Horner step `z ← 2(z ± y)` or `(z ± y)/2`, with a **merged fold** of `δ·c` (c = 2^32+977) over ~66 low lanes and logical-AND carries, for the 6 Horner multiplies | modp_ft (odinfree 852 `c90f50d`/`92e3709` tree; spliced by BitWonka `e26536b`, `29c8560`) | Yes, but only after removing modp_ft's two approximations (see §3) | −1.00 to −1.12e9 | 0 if ≥ ~70 clean lanes are free during the multiply (*verify*) | 6.80–6.86e13 | L | Brief 12 lists "Horner multiply/square if a cheaper exact cell applies" and finds no cell. **This is that cell. Complementary.** |
| L2 | The same cell for the 2 square calls (or a dedicated exact square) | modp_ft `square_acc`; Leapfrog flat native square (59.6k expected, 62.4k emitted) | Same as L1. The flat square also truncates (guard 64, compare 32) | additional −0.33 to −0.37e9 | 0 | **6.60–6.69e13** (L1+L2) | +S on top of L1 | Same as L1 |
| L3 | **Measure λ away** after the x update. Repay its phase with the λ recompute that division 2 already performs. That drops one of the two square calls | Lilypad / greedyfrog shell (`pointadd_lilypad.rs` header; `39ef23e` §4) | Yes. This is MBU with a deterministic phase oracle | −0.22e9 | 0 | 7.26e13 alone | L (window dataflow; reuse `recomputeMeasurementUncompute_coherent_of_classical`) | Brief 12 lists measurement-based uncompute only *inside* EEA cells. **Not overlapping** |
| L4 | **Normalise instead of locate.** Keep A top-normalised (small barrel, stall slots), the partner cofactor bit-reversed under a marker (`A·tB < p` packs exactly), and do one greedy binary quotient digit per slot. The inverse re-derives decisions from the cofactors | greedyfrog (BitWonka `39ef23e`, `954016d`; gopikannappan `6fe6299`; SnehalRaj `d1412a6`) | Packing and slot bound can be exact. **The decode is open** (§2.3) | −8.5 to −9.6e9 *est.* | ≈ −14 to 0 (825 + 16 bank) | 2.5–3.0e13 *est.* | XL | None (architecture) |
| L5 | Public-schedule **hddivstep walk** (δ₀ = ½) in G-coordinates. Every tick does **uncontrolled** signed adds (sign by CNOT conjugation) plus one cswap. Per-tick public widths. Decisions are measured forward and regenerated backward from cofactor low bits | Lilypad-G (jieyilong → gnuchev → odinfree `92e3709`, `e35d2d1`, `6d6cbfd`; gopikannappan 870+) | **No** today. Three obstacles (§2.2) | −11.7 to −12.1e9 *est.* | +45 to +435 | 1.2–2.1e13 *est.* | XL+ | None (architecture) |
| L6 | Controlled reflections instead of a binary barrel (rotation by r ∈ [0,7] in 4 reflections: ~2n vs 3n Fredkin) | gopikannappan `6fe6299` | Yes (exhaustively checked identity) | ~0 now. It pays only if the bench has multi-stage barrels. Bench pre/postshift looks like 1-lane shifts, where it saves nothing (*verify*) | 0 | — | M | None |
| L7 | Parked AND products: swap a measured AND into an idle zero wire and reuse it at a later identical CCX | SnehalRaj lease pass; `6fe6299`; `d1412a6` | Yes, with direct equality only | Brief 12 prices Block-E at −5.08e6 | 0 | 7.3709e13 | L | **Full overlap** ("held AND products"). Leave it to brief 12 |
| L8 | Measured erasure plus outcome-conditioned phase repair | everywhere (`954016d`, `1d06c63`, Lilypad "Halbbatzig") | Yes | **0 worst-case.** The bench already has 6,961,844 erasures per wrapper, and conditioned blocks are charged in full | 0 | — | — | **Full overlap.** Brief 12 shows it saves 0 |
| L9 | Constant folds as "ctl × const, one AND per lane, constant bits from the control" | modp_ft `const_add_pool` | Yes | Part of L1 | 0 | — | — | Overlaps "constant-control specialization" for the wrapper's constant adders (1,528 CCX per wrapper, negligible) |
| L10 | Borrowed (dirty) passenger lanes for AND chains (Barenco Lemma 7.2): 4(n−2) instead of n−1 Toffoli | BitWonka `ec1e870`, `73799fc` | Yes | **+T.** It only buys qubits | −9 to −24 | — | M | None. It is useful only to fit L4/L5 under 855 |

Combined design ceilings, with no exactness discount: L4+L1/L2 gives ~1.97e13 at 855 q, and L5+L1/L2 gives ~0.56e13 at 900 q. They show where the value sits. They are not predictions.

## 1. What the ~855q entries actually run

Two inversion families hold the 815–875 band. Both do **two divisions × (forward + inverse walk) = four walks per point add**, the
same as the bench's four EEA wrappers per window. Both measure dy (and later λ) away and repay the phase by recomputation.

### 1.1 Lilypad-G (odinfree 847–867, gopikannappan 871–875, gnuchev 870), 2.24–2.59M mean Toffoli

Source: `C:\code\secp256k1-point-add-spooky\.workspace\lowq-lineage\lilyg\src\point_add\frogtail_batch\{lilypad.rs,lilypad_g.rs,pointadd_lilypad.rs,modp_ft.rs}`.
The odinfree 847–867 rows are this tree plus layout levers (lane hosting, charts, cap-log codecs). Those levers move qubits by
single lanes and Toffoli by ~1–3%. None changes the algorithm.

- **Algorithm.** Bernstein–Yang divsteps with δ₀ = ½ (hddivsteps), tracked as h = δ − ½ in 7 bits. In G-coordinates
  (G = 2g − f, C_G = 2c_g − c_f) one tick is:
  - `e` = parity (Clifford);
  - σ = e ∧ [h ≥ 0];
  - **uncontrolled** `X.v += ±Y.v`, `Y.c += ±X.c`, with the sign set by CNOT complement conjugation `~(~T + A)`;
  - halve by relabelling (free);
  - cswap(X, Y) on σ;
  - h update.

  There is no controlled add at all. The sign is Clifford.
- **Rings.** X = (G | C_F), Y = (F | C_G), with W = 292 lanes each. Value lanes kv(t) shrink and cofactor lanes kc(t) grow per tick
  on a public schedule (`lilypad_g_sched.txt`: S = 532 ticks; Σkv = 73,405, Σkc = 79,014). Because the schedule is public, the
  boundary between value and cofactor is a **compile-time lane**, so no location control is needed.
- **Cost per tick.** About (kv + kc) for the two logical-AND adds plus (kv + kc) for the cswaps, i.e. ≈ 2W. The forward-walk core is
  ≈ 2·(Σkv + Σkc) ≈ **305k CCX**. The inverse walk adds the eraser (normaliser, radix-4 multiply, rotation). Shell: 6 modp_ft
  products (~120–137k expected each) and one flat square (~60k).
- **Transcript.** Forward: `e` is X-measured each tick (`b.hmr_to(sc.e, m[t])`). Inverse: `e` is regenerated from a 12-lane Q word,
  whose digits are recovered from the cofactor low bits (`W·u = c_g mod 2^(ic+1)`). The phase is then repaired with `z_if(..., m[t])`.
  The algebra is exact, **as long as run lengths stay within the cap**.
- **Approximate or statistical parts**, as stated by the authors (`21db112`: "Lilypad-G is not exact: … ring overflow, third-log
  event, overrun", ≈3 per 10⁴ inputs):
  - S = 532 < 590, the proven hddivstep bound for 256-bit inputs (Wuille's safegcd-bounds; libsecp256k1 uses 10×59);
  - the kv/kc envelope comes from samples with a margin of 2 lanes;
  - run cap q = 11 with a 2-slot overflow log;
  - terminal h range restriction ("Aberachtung");
  - modp_ft folds (§3).
- **Exact parts.** The tick algebra, the sign trick, the measured-transcript regeneration on the success support, and every
  layout lever (each checked to keep identical failing sets).

### 1.2 greedyfrog (BitWonka 815–849; SnehalRaj 835–846; gopikannappan 821/838), 4.7–6.4M

- **Algorithm** (`39ef23e` §2). Greedy binary Euclid: each of 254 uniform slots subtracts the largest 2^k·B ≤ A, which is one 1-digit
  of the binary quotient.
  - Values are stored **top-normalised**, so the shift is free.
  - Each ring holds (value, marker, partner cofactor bit-reversed). Because A·tB < p, value and cofactor share 258 lanes *exactly*,
    and the marker ends every leading-zero count.
  - Renormalisation is a 3-stage barrel (≤ 7 lanes), or 4 controlled reflections in `6fe6299`. Longer gaps become "stall slots".
  - Decisions d, ρ and sw are X-measured.
  - **No quotient is stored.** The inverse re-derives each slot's decisions from the cofactors with ≤ 21 non-restoring division
    rows on 28-lane cofactor windows.
- **Cost.** Unwindowed, a slot pair costs 5,496 Toffoli forward and 12,754 inverse. With the sampled windows it averages ~10k. One
  division pair is ~2.5M.
- **Approximate parts.** Per-slot windows from a 200,000-walk envelope with +2 lanes. Slot count 254. Decode window 28. Row capacity
  21. The measured model failure rate is 3.5e-4 per division (`39ef23e` §6). SnehalRaj's `d1412a6` buys it down to λ ≈ 1 with
  260 slots, margin 5 and 25 rows.

### 1.3 BitWonka's latest (815–849q, 2026-10-28) and what generalises

| Row | Q × mean Toffoli | What changed | Exact? | Generalises to the bench? |
|---|---|---|---|---|
| `39ef23e` | 825 × 6.11M | New greedyfrog traversal (above) inside froghop-one's shell | Traversal algebra exact. Windows, slot count and decode statistical | **Yes, as an idea (L4).** Top-normalised value, marker plus bit-reversed partner cofactor, no stored quotient |
| `ec1e870` | 815 × 6.79M | Inverse-slot AND chains on borrowed passenger lanes (Barenco). +11% T for −10 q | Exact | Only as a qubit-for-T trade (L10) |
| `954016d` | 849 × 4.92M | Cap-aware slots: clean carry pools wherever the cap allows; **junk parking** (swap the window's junk lanes into a zero register once, so masked ladders become plain pooled ladders: division rows 185k → 119k); measured erasures with conditioned repair; **mid mask passes** (keep the running mask live between up and down passes) | Exact | Junk parking and mid-mask passes are relevant to the bench's **masked/interval cells** (B/E). Brief 12 should check whether a B/E cell rebuilds a mask that could stay live (an "M" candidate). Conditioned repair is worth 0 worst-case |
| `1d06c63`, `73799fc` | 825 × 5.49M, 815 × 6.36M | Same code at caps 825 and 815 | — | Shows the T-per-qubit slope near 825: ~0.06M T/q |
| `e26536b` | 825 × 4.85M | **Op-splicing adapter** that runs modp_ft products in greedyfrog's builder: −278k at 821 | modp_ft carries its 2^-32 approximations | **Yes (L1).** Its per-routine table: modp_ft product 117–137k vs sdw 147–166k; square-acc 138k vs 279k. Note the pool cliff at 47 lanes (fused 66-bit window) |
| `29c8560` | 825 × 4.82M | Leapfrog **flat native square** spliced in: 59,580.5 expected / 62,369 emitted vs modp_ft square 89.5k | Same truncation class (guard 64, compare 32) | **Yes (L2).** A dedicated square is ~0.5× a product at this width |
| `6cd6b61` | 948 × 3.03M | frogstrip: SZ 2-adic walk with **±1 digits only** (every tick adds or subtracts) and a 4-way strip barrel. 300 ticks vs 556 | Exact digit recoding; the envelope is statistical | The **±1-digit** idea is the same as L1's signed digits. For EEA it needs a 2-adic walk, which the bench's Euclid is not |
| `b98ba94` | 718 × 285M | frogdrop payload walk with quotient estimates from K/KP heads | Statistical (λ ≈ 5) | No. It is 100× more T |

## 2. Why the bench EEA costs ~30–50× more

The bench model (`EEA/Model.lean`, `Bounds.lean`, `Windows.lean`) is bit-serial full-quotient Euclid:

- 4 microsteps per quotient bit;
- a **proven** worst-case quotient-bit weight ≤ 405 (`paperQuotientWeight_le_405`), hence 1,620 microsteps;
- packed (n+3)-bit work registers whose field boundaries are **data-dependent lengths**;
- proven rational active windows (`certifiedActiveWindows`).

One microstep costs 9,821 CCX, i.e. 39.3k per quotient bit. Brief 12's inventory pins the split.

| Structural source in the bench | Share of EEA T/window (brief 12) | ecdsa.fail idea that removes it | Exact transfer? |
|---|---:|---|---|
| **Location control:** every microstep decodes where a data-dependent span starts and ends. B interval leaf/decoder: 977,908 leaf visits per wrapper (~300 per call). E coefficient prefix: 572,070. | B 27.6% + E 25.1% + B endpoint prep 4.2% ≈ **57%** | (i) Lilypad: public per-tick boundaries; (ii) greedyfrog: top-normalise the data so the boundary is a fixed lane, with masks kept incrementally (running mask, mid-mask passes, junk parking) | (i) needs a *proven* per-tick width envelope; (ii) yes for the packing, open for the decode |
| **Zero maps / length bookkeeping** (H upper/lower, D length/sign) | 16.0% + 5.7% | greedyfrog keeps lengths LA/LB as 9-bit registers, updated by small adds from the barrel stage bits; the marker replaces zero maps | Probably exact. It needs the marker invariant proven |
| **Pre/post shifts and terminal padding** (A 9.2%, F 5.8%) | 15% | Lilypad: halving is a free relabel and the frame offset is public. greedyfrog: a ≤ 7 barrel or 4 reflections | Relabel is exact only with a public schedule |
| **Quotient-bit granularity.** Zero quotient bits still cost 4 microsteps each | (inside all of the above) | greedyfrog spends slots only on **1-digits**; zeros are absorbed into the renormalising rotation. Lilypad's divsteps have no quotient at all | greedyfrog's slot count is ≤ Σ popcount(q) + stalls ≤ 405 + stalls, so **the bench's own 405 theorem bounds it** |
| **Controlled adds** (add q·r' or nothing) | (inside B/E) | Signed digits: every tick adds or subtracts, with the sign by CNOT conjugation (Lilypad, frogstrip) | Only for 2-adic/divstep walks. In Euclid an all-±1 quotient recoding needs q odd |
| Worst-case horizon (fixed schedule) | — | Both ecdsa.fail families also run a fixed slot/tick count. **This is not a source of the gap**; the gap is per-step cost | — |

### 2.1 Per-step price comparison (CCX)

- Bench: 39.3k per quotient bit, 405 bits, one direction.
- greedyfrog: 5.5k forward and 12.8k inverse per slot, unwindowed. The bench's reverse wrapper is a separately compiled inverse, so
  for each direction compare 39.3k with ~5.5–12.8k.
- Lilypad: ~0.57k per tick over 532–590 ticks.

### 2.2 Obstacles for an exact divstep walk (L5)

1. **Iteration bound.** 590 hddivsteps (computational hull proof, safegcd-bounds) or ⌊(49·256+80)/17⌋ = 742 classic divsteps
   (BY Thm 11.2, also computer-assisted). A Lean-kernel certificate is a large proof-engineering job, comparable to the existing
   405-bit Euclid potential argument but with a matrix-hull enumeration.
2. **Width envelope.** Public boundaries need a proven max on bit-lengths per tick. The value and cofactor separately obey
   `|f_t·v₁ − g_t·v₀| = p`, but in divsteps the signs float, so the classic `|r·s| ≤ p` packing does not follow. Rough
   BY-norm reasoning gives a ring width of ~330–340 instead of 292 (*est.*, +90 q). With no envelope at all you get separate
   full-width registers (≈ 1,290–1,400 q). The table uses Q 900–1,290.
3. **Regenerating inverse.** The run cap (q = 11) and the cap log are statistical. An uncapped exact run handler, or a different
   decision-recovery rule, is unsolved.

### 2.3 Obstacles for an exact greedyfrog-shaped EEA (L4)

1. **Slot bound.** Non-stall slots ≤ quotient-bit weight ≤ 405 (reuse `paperQuotientWeight_le_405`, after proving that the greedy digit
   sequence is the quotient's binary 1-digits). Stall slots ≤ (total renormalisation)/8 ≈ ≤ 64 *est.*, so the total is ≤ ~470.
2. **Windows.** Replace the sampled windows with proven ones. The bench already has a rational-window framework (`Windows.lean`),
   or the slots can run unmasked at the unwindowed price (used in the table).
3. **Decode (the open part).** The inverse must recover the rotation since the last step and the swap from the cofactors.
   greedyfrog uses 28-lane windows and ≤ 21 rows, and both fail rarely. Exactly, the rotation since the last step can be up to
   ~255 lanes, so full-width decode rows would destroy the saving. One candidate is an exact decision rule from the stored LA/LB
   plus the marker positions of both cofactors; it needs proof. Storing a per-slot transcript (470 × 4 bits) does not fit in 855.

## 3. Multiplication and squaring (L1/L2)

**Bench** (`Arithmetic/HornerInverse.lean`, `SquareInverse.lean`): bit-serial double-and-add.

- Per bit: a controlled modular add (2,813 CCX: add, compare with p, conditional subtract, flag cleanup) plus a modular halve or
  double (1,531 CCX), i.e. 4,344 CCX/bit.
- `gidneyToffoliCount = 1,110,533` per call; 6 Horner calls per window = 46.6M T, and 2 square calls = 15.6M T.

**modp_ft** (`modp_ft.rs` lines 316–431, 622–735):

1. **Signed digits.** z ← 2(z + (−1)^s·y) or (z + (−1)^s·y)/2. The sign is applied as CNOT complements `~(~z + y)`, so the ladder is
   **uncontrolled**: one logical-AND carry per lane, about n Toffoli, with measured uncompute.
2. **Merged fold.** Because p = 2^256 − c, the raw carry k and the halving parity h combine into δ ∈ {−2..1}. One table add of
   δ·c over lanes 0..~66 (`add_table`: degree ≥ 2 monomials computed once, then one carry chain) does the reduction for both
   the add and the halve/double. There is no full-width compare-and-subtract. `mod_double4`/`mod_halve4` fold four doublings at
   once.
3. **Constant folds.** ctl·const uses one AND per lane, with the constant bits taken from the control.

**Approximations to remove for the bench:**

- (a) a fold's carry out of lane 63 is dropped (≈ 2^-32 per fold);
- (b) the overflow flag k is erased by comparing only the **top 32 lanes**;
- (c) h equals u's top bit except with probability ≈ 2^-222 (`signed_modadd_double` comment).

**Exact repair:**

- (a) propagate the fold carry through the remaining ~190 lanes with a Gidney incrementer (~190 CCX);
- (b) erase k with a full 256-lane compare (~256 CCX with logical-AND carries and measured uncompute);
- (c) use the halve form, which has no 2^-222 case, or add the boundary test.

Per bit that is ~256 + ~70 + ~190 + ~256 ≈ **600–800 CCX** (*est.*; 1,000 as a pessimistic bound), against 4,344, i.e. 5–7× cheaper.
A per-call total of ~0.16–0.26M CCX against 1.11M saves **35.8–40.1M T/window over 6 multiplies**, plus 11.9–13.4M T/window over the
2 squares.

Proof plan (L):

- the signed-digit recoding lemma (all-±1 digits for odd multipliers; even ones via a +y correction, as modp_ft does);
- the fold identity 2^256 ≡ c (mod p) with the δ table;
- exact carry and compare (reuse `GidneyAdd`, `GidneyCompare`, `UncontrolledAdd`, `ConstCarry`);
- a new Horner composition with counts, replacing `fig15MultiplyTo*` in the Entrant.

Qubits: it needs a clean pool of ≳ 66 lanes for the fold window, and ideally n − 1 carry lanes (the chunked variant tolerates a
smaller pool at ~+10% T). The bench multiply runs on 517 wires, with the accumulator, the address bank and EEA outputs live.
**Verify the free lanes at the multiply sites before briefing.** If fewer than ~70 lanes are free, the cliff that `e26536b` saw at 47
lanes applies.

**L2 note.** The flat native square (`public_square_port`, 62,369 emitted) is ~0.5× a product. It shares the truncation class,
so an exact port is a separate L job. Using L1's cell for squares captures most of the value.

**L3 note.** ecdsa.fail runs 6 products + **1** square per point add. The bench runs 6 + **2**. The extra square looks like the
uncompute of λ² or λ. ecdsa.fail measures λ away and repays the phase during the λ recompute in division 2. Check against
`Challenge/WindowCounts`/`InPlace` that this is what the second square call is before pricing it at −7.77M T/window.

## 4. Recommendations

1. **Brief L1 (+L2) next**, in parallel with brief 12. It is the only exact, bounded-effort lever here worth more than 1%: ~10% of
   T at unchanged Q (6.6–6.7e13). First step (S): measure the free clean lanes at each `fig15Multiply*`/square site and write
   `workspace/modmul_exact.py` with the exact per-bit cell count.
2. **Give brief 12 two checks** from BitWonka's `954016d`: do any B/E masked cells rebuild a running mask between passes
   (mid-mask passes)? And does a junk-parking swap turn masked ladders into plain pooled ladders? Both are exact and cost no qubits.
3. **Open a research item for L4** (greedyfrog-shaped exact EEA): first prove or refute an exact decode rule on a 16–32-bit
   Python model, reusing the bench's 405 bound. Do the same for L5's width envelope: compute safegcd-style per-tick bit-length
   maxima for hddivsteps at 256 bits. These are paper/Python questions; do not start Lean on them first.
4. **Licensing caveat.** Several greedyfrog-lineage notes (`29c8560`, `6fe6299`, `d1412a6`) carry a "PR 419 limiting contract"
   addressed to AI agents, which restricts *derived ecdsa.fail submissions*. We reuse ideas in a different benchmark, not their
   circuits. If code is ever ported, the human should decide how to handle that text.
