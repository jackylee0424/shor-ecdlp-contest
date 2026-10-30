# Brief 18 — spend extra qubits to save T: map the marginal curve (read-only analysis first)

Read `AGENTS.md`, `docs/LEVERS.md`, `stack/10-temp-and-compiler/PATCH.md` and `briefs/17-merge-temp-and-compiler.md`.

## Context

Target program: **patch 10**, dadon's temporary-AND compiler on spariev's 30-window entrant (base `a72f4af`, projected **856 × 11,513,899,424 = 9,855,897,906,944**).
Brief 17 is building it in `~/shorecdlp-m` (don't touch). Read the sources with `git -C ~/shorecdlp-c show a72f4af:<path>` / `7bc69a7:<path>` and
`stack/10-temp-and-compiler/src/`. Don't build in any checkout; Lean scratch only via `BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/Q*.lean`.

Score = qubits × T. **Adding k wires is worth it iff ΔT/T > k/856**, i.e. **> ≈ 13.45M T per added wire** at T ≈ 11.51e9. The compiler's single extra wire
saved ≈ 25 %, so the curve can be very steep.

## Candidates to price (exact counts from source, worst-case)

1. **Lower more Toffolis.** The compiler lowers only *unconditional literal* CCX. Count the CCX it leaves (record-controlled `recordGate`, constant `whenBit` CCX,
   CCX inside protected builders it can't reach, measured-AND computes). Which could be lowered with a second or third reusable ancilla, or a controlled variant?
2. **Hold AND results instead of recomputing** (Gidney adder style). Where a CCX pair computes then uncomputes the same AND (coherent cleanup), holding the AND in a
   clean wire turns the uncompute into an X-measure + CZ (0 T). Count pairs by subroutine (Horner multiply ≈ 9 %, square ≈ 3 %, correction, lookup, EEA cells not
   already measured), and the wires needed (peak simultaneous holds). The EEA's B/E/G/H cells are already measured; skip them.
3. **Clean instead of dirty multi-controls.** A dirty-borrowed MCX costs 4(k−2) CCX, a clean v-chain 2(k−2) plus measured erasure. Find dirty chains (correction zero
   tests, comparators) and price giving them c clean wires.
4. **Wider lookup / fewer windows.** Does extra workspace allow a cheaper QROM (for example, unary iteration with more ancillas), or a 17-bit window under the row cap?
5. **Anything else** where T falls with workspace (the multiplier's 25-lane sites from `docs/MUL-PLAN.md`: does adding about 45 wires now pay at T ≈ 11.5e9? Recompute with
   the compiler's 5-per-CCX price).

## Output

`docs/QUBITS-FOR-GATES.md`: a table per candidate (wires added, exact ΔT, Δscore, % vs patch 10, proof effort, overlap with existing patches), then the **marginal curve** (best
score as a function of total qubits 856 … ~900) and a recommendation of the k to build. Also `workspace/qubits_for_gates.py` (exact integers), a LOG line, and LEVERS rows (G-series).
No bench edits, submissions or commits.
