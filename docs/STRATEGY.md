# Strategy notes (living — edit freely, keep it short, date your additions)

## Score levers

`score = qubits × tModel`. The shipped entrant is at ~2.07e5 qubits × 3.55e14 T, while the paper
design is ~8.5e2 × 8.0e11. Both factors have orders of magnitude of headroom.

1. **Qubits (×~240 available).** The Naive workspace is "dense": a fresh wire for every intermediate.
   Levers: semiclassical (one-qubit, measure-and-reset) phase estimation instead of two 265-qubit
   registers; in-place modular arithmetic with uncomputation and reuse of scratch; and the
   2607.13816 streaming layout (854 wires).
2. **T (×~440 available).** Levers: windowed scalar multiplication against the coefficient table
   (lookup + add instead of controlled double-and-add); specialized secp256k1 reduction
   (p = 2^256 − 2^32 − 977); cheaper inversion (EEA-based, as in 2607.13816, instead of Fermat);
   cheaper adders (Gidney/Cuccaro-style, CCX count ≈ n per add); and fewer trials.
3. **Trade-offs.** More trials with fewer phase bits (the `wrappedShift` decoder) versus one
   high-precision trial (`nearestPair`). The candidate-check budget (~2^55) allows the paper's 56 trials.

## Proof-reuse map

- `Submission/Naive`: complete certified correctness, success probability and resources.
  Most reusable for arithmetic correctness.
- `Submission/2607_13816`: in-progress streaming construction. Its outer program, resource
  interface (`OuterBudget`), Fourier feedback and EEA pieces exist; window bodies, success and
  resource instantiation remain. See its `INTEGRATION.md` and `REFERENCE.md`, and the bench
  `docs/STREAMING_*.md`.
- The Entrant may import anything in the bench (Naive, 2607_13816, Framework, Math). It cannot change those files.

## Candidate directions (rank and update)

| # | Idea | Expected effect | Effort | Status |
|---|---|---|---|---|
| A | Semiclassical QFT (1 control qubit + feed-forward `P` via `recordGate`) on top of the shipped entrant | qubits −~528 (small relative to 206k) | M | open |
| B | Reduce dense workspace: reuse scratch wires in Naive arithmetic | qubits ÷ large | L–XL | open |
| C | Finish the 2607.13816 streaming certificate inside Entrant | ~1e5× better score | XL | open |
| D | Cheaper T inside Naive arithmetic (adder/reduction swaps) | T ÷ 2–10 | L | open |

Seed analysis tasks: quantify where the shipped entrant's qubits and T come from, per subroutine,
before choosing a direction (`work-notes/HANDOFF.md`).
