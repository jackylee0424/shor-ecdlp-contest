# WEX: what we missed and how to generalize it

Re-scan and analysis, 2026-10-30. The arithmetic is in `workspace/wex_levers.py`. Every figure below is a **projection from public notes; nothing here is proved**.
Sources: `research/yukon-notes-wex-6ee2945a.md` and `research/yukon-notes-wex-f1518daf.md`, plus the ecdsafail-lean clone at WSL `~/research/ecdsafail-lean` (read-only, untrusted).

## Verdict

The new leader is ArthurOstapenko `f1518daf`: **1,932 Q × 348,877,454 T = 674,031,241,128**.
It keeps the 29-addition streaming producer and its success proof unchanged. It replaces the EEA-based point addition, which costs about 509M T per addition, with
**ECDSAAdd**: the Lean-certified, Apache-2.0 controlled affine point adder from the sibling Yukon challenge `eigenlabs/ecdsafail-lean/lean`
(benchmark `b58da34e`), pinned at `c3f340a` (≈1,899 Q, 2,216,363 Toffoli). The Q×T entry of the WEX body is 4 T per CCX with about 3.0M CCX per addition.

**The sibling challenge has moved since then.** Its leader is `0b650bb`, at **1,594 Q × 2,155,232 Toffoli**: 305 fewer qubits and 61k fewer Toffolis than the adder WEX copied.
Swapping that adder into WEX projects to **≈5.56e11 (−17.5 %)**, which clears our >10 % bar.
Fusing lookup traversals and measured unlookups could stack another 4–11 percentage points on top.

## What we missed (root causes)

1. **We never looked at the sibling Lean challenge.** We audited ecdsa.fail's Rust/qubit-layout notes (`docs/ECDSAFAIL-TRICKS.md`, `ECDSAFAIL-855.md`) and ecdlp.ai Gold (`ECDLP-AI-GOLD.md`).
   Both are *uncertified* circuits, so we judged a port to be months of work (Gold milestones M0–M4).
   The challenge `ecdsafail-lean` was producing exactly the missing piece: a kernel-checked adder in a compatible gate set. Yukon lists it with `yukon benchmark list`, and we never ran that command.
2. **We priced the right idea with the wrong producer.** `ECDLP-AI-GOLD.md` §4 already found "19–77× arithmetic-only headroom" for a ~1,240–1,760-Q affine adder.
   It priced the adder with 464 binary additions over 26 rounds, which gives 3.1e14. The windowed streaming producer (29 additions, with 15-bit coherent lookups supplying the table constants as leaf `whenBit` gates)
   turns the same adder into 7.3e11. We never redid that pricing after the producer changed.
3. **Our qubit-trade studies were marginal and stuck on the EEA design.** Briefs 18 and 21 (`QUBITS-FOR-GATES.md`, `FEWER-QUBITS.md`) only tested adding or removing a few wires around 856.
   We had diagnosed the bench EEA as "~30× dearer" (C7c), but we only tried to shrink it (fast multiplier, divsteps) and never to replace the whole addition.
   **Lesson:** when one component is 30× worse than the literature, look for a certified drop-in replacement before trying to optimize it.

## Generalizations (levers on the WEX leader)

| # | Lever | Mechanism | Projected Q×T | vs leader | Main risk |
|---|---|---|---:|---:|---|
| W1 | **Adder swap to the ecdsafail-lean frontier** (`0b650bb`, 1,594 Q × 2,155,232) | Re-run the WEX port (lookup holes for `cx, cy`, coherent specialization, one-row negative-double corner, native→Streaming transport) on the newer adder. Q ≈ 1,932 − 305 = 1,627 | 5.56e11 (+8 wires overhead: 5.59e11) | **−17.5 %** (−17.1 %) | The newer adder must stay uniform in C apart from constant bits (its `program L cx cy` signature suggests it does). Entrant size: the newer adder is 74k Lean lines, and the WEX base replay already peaks at 65 GiB of the 78 GiB gate. Race: ArthurOstapenko is active in both challenges |
| W2 | **Traversal fusion** | f1518daf merged parity into the finite/X leaves (32→28→24). Any loads whose targets are idle at the same time, with commutable segments, can share one traversal, because leaves are whenBit gates on distinct targets. Each traversal removed per addition saves 3.80M T | 24→16: 5.07e11 | −24.8 % (with W1) | Needs a liveness/commutation census of the adder's 24 load sites |
| W3 | **Measured unlookup** (Gidney-style) for compute/uncompute load pairs | Unload by X-basis measurement plus a phase lookup on a √-split address, at about 2·2^8 CCX instead of 32,767. It needs 2^7–2^8 clean wires *borrowed from idle adder workspace* | 8 pairs: 5.07e11; 12 pairs: 4.83e11 | −24.7 % / −28.3 % (with W1) | If the wires can't be borrowed (+128 Q), only −18.8 %. Needs the phase-lookup proof over coherent addresses |
| W4 | Track the ecdsafail-lean frontier continuously | Each new adder record ports with the same transport. One percent fewer adder qubits gives about 0.8 % lower Q×T here (the adder is ~98 % of the wires); one percent fewer Toffolis gives about 0.73 % (≈73 % of the body) | — | — | Port cost per refresh. Make the transport parametric in the adder |
| W5 | Our own adder work | Gold 1,240–1,300-Q routes would be −20 % Q again, but they are approximate and uncertified (M0–M4). The certified frontier now sits at 1,594 | — | — | Months; low priority unless the sibling frontier stalls |

The old 856-Q EEA line (spariev, dadon, kaankolcu, ~6.9e12) is now 10× behind. Our open EEA, divstep and fast-multiplier levers are moot.

## Suggested order

1. **W1 feasibility** (Codex Daybreak, read-only first). Diff the WEX vendored parts (`c3f340a`) against `0b650bb`. Confirm the new adder is a `cx, cy`-parametric uniform program.
   Find where WEX's lookup holes and transport attach. Estimate the Entrant size and replay memory. Then build it in `~/shorecdlp-c` on bench `60ccc81`.
2. **W2 census:** list WEX's 24 traversals with their targets and live ranges, and the fusion candidates.
3. W3 only after W2, because it competes for the same traversals.

Submissions stay on hold. W1 alone would clear the >10 % rule, so it is a decision point for lifting the hold.
