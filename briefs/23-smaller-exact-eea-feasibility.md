# Brief 23 — feasibility of a genuinely smaller/cheaper EXACT inversion to replace the bench EEA (read-only research, XL)

Read `AGENTS.md`, `docs/LEVERS.md` (C7a/b/c, B6/B7), **`docs/ECDSAFAIL-855.md`** (Lilypad-G divsteps ≈ 0.30M Toffoli/walk vs 15.9M per bench wrapper; greedyfrog
top-aligned Euclid; ~57 % of bench EEA T is locating data-dependent register boundaries), **`docs/FEWER-QUBITS.md`** (the EEA phase occupies all 855 wires; per-qubit
ceilings 855 → 800), `docs/EEA-INVENTORY.md` (exact per-cell counts), `docs/ECDLP-AI-GOLD.md` (exact Gold cells, M0–M4), and arXiv:2607.13816 **v3** (835 qubits; inversion
2n + 6⌊log₂n⌋ qubits and 229n² Toffoli).

## Base

Leader **spariev `c96133a` (bench `32b7d38`): 856 × 8,480,934,044 = 7,259,679,541,664**, 29 windows, 4 EEA occurrences per window (two divisions in multiply/divide form),
4-P catalyst lowering. EEA is still the dominant cost (≈ 87 % of window T before lowering). Submissions are on hold.
Lean scratch only via `BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/EEA2*.lean`. Never build in `~/shorecdlp` (brief 22).

## Questions

1. **Candidates.** Price exact, worst-case versions of: (a) Bernstein–Yang divsteps with a **proved** iteration bound (the published bound for 256-bit inputs, e.g. ≈ 590–744
   divsteps, not the sampled 532), fixed widths, and constant-time conditional swaps/negations; (b) greedyfrog-style top-aligned Euclid with exact (not sampled) windows and full
   decode; (c) arXiv v3's 2n + O(log n) inversion; (d) a hybrid that keeps the bench EEA's verified semantics but removes the per-microstep boundary location (the ~57 % term).
   For each: qubits (it must fit the leader's peak budget or justify extra wires with brief 18/21's thresholds), worst-case CCX → T under 4-P lowering, records, and the inversion's
   contract (does it produce exactly the bench EEA's output, so the window code can reuse it, or does the point-add wrapper change?).
2. **Proof route.** What is the minimal set of new Lean theorems (divstep correctness and termination bound, the fixed-schedule circuit, exact counts, the interface
   to `fig15` division/multiply)? Which bench lemmas transfer? Give an honest S/M/L/XL breakdown and the main risk.
3. **Projection.** Exact projected T and Q×T for the best candidate on the leader (29 windows × 4 EEA occurrences), and the % vs 7,259,679,541,664.
4. **Verdict** with stop conditions, and a recommended first milestone (for example, a kernel-checked divstep iteration bound plus a small-width exact circuit).

## Output

`docs/SMALLER-EEA.md` (verdict first), `workspace/smaller_eea.py` (exact integers), Lean scratch if useful, a LOG line, and LEVERS C7 rows. No submissions, no bench edits, no commits.
