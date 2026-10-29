# Brief 05 — quantify the levers for our contributions on top of the upstream streaming certificate

Read `AGENTS.md`, `docs/PRIOR-WORKS.md`, `docs/RELATED-WORK.md` and `briefs/04-port-upstream-streaming-26-rounds.md` first.

## Context

Brief 04 (running concurrently: **do not build, edit or run lake in `~/shorecdlp`**) ports upstream VerifiedQC
`lamport/challenge-final-certificate` @ b46e337 into Entrant and cuts it to 26 rounds: 3,932 qubits × 374,227,740,666 T ≈ 1.47e15.
We want **our own contributions stacked on top**, ideally techniques from our prior work (`/mnt/c/code/secp256k1-point-add-spooky`,
`~/r21-lean`). Read upstream code with `git -C ~/shorecdlp show upstream/lamport/challenge-final-certificate:<path>` and
`git -C ~/shorecdlp grep ... upstream/lamport/challenge-final-certificate -- <paths>` (existing protected modules: `origin/master:<path>`).
This task is read-only analysis plus Python in the lab's `workspace/`.

## Three levers to quantify

1. **Qubits.** Support = wire 837 :: `batchedResetWires` (length 3931; `CompleteSupport.lean`, `BatchSupport.lean`, protected
   `WindowBody.lean` / `resetWires` / `windowAddressPerm` / `batchPlacement`). Explain exactly why 3,931 distinct labels are used: which
   lifetimes overlap and which are fresh only for proof convenience. Design a reallocation that reuses labels, and give the minimal
   achievable support with a justification (target: near the legacy 854/~870). Say which protected definitions the Entrant would have to
   re-define (Entrant can import protected builders but cannot edit them), and which upstream proofs would have to be redone. Size it (S/M/L/XL).
2. **Per-round acceptance.** `DecoderBridge.wrappedIdeal_mass_lower` proves 163/1000 ≤ `reducedRawIdealFourierEventMass`. Find the
   formula and evaluate the **true** value numerically (`workspace/round_mass.py`). Find where the proof loses mass. Tabulate the required rounds
   (1 − (1−p)^r ≥ 0.99) and the T for a few achievable p values, and say how hard a tighter Lean bound would be. Note that the decoder
   kind and params (wrappedShift, 256/208 bits) are fixed by the layout and candidate budget, so check whether changing `rightBits` (window
   counts or Fourier bits) helps.
3. **T per round (14,393,374,641).** Break it down by component (windows, batched correction `BatchCost` 3,784,382 per placement,
   Fourier feedback 54,168, ...) in `workspace/streaming_t_breakdown.py`. Map our prior techniques (AND-erasure with 0 T + CZ repair,
   phase-only carries, cheaper adders) onto specific components, and estimate the saving and proof effort for each.

## Output

`docs/CONTRIBUTIONS-PLAN.md`: a ranked table of our contribution candidates (gain on Q×T, effort, risk, which of our prior work it reuses),
then a concrete implementation brief outline for the top two (files to add under Entrant, upstream lemmas to reuse, proof obligations).
Add a LOG line. Do not edit HANDOFF's "In flight" rows owned by brief 04.
