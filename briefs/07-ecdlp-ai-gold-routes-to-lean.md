# Brief 07 — ecdlp.ai Gold routes: what can become a Lean-certified circuit for this challenge

Read `AGENTS.md`, `docs/PRIOR-WORKS.md`, `docs/RELATED-WORK.md` (§4 Gold), and `briefs/06-ecdsafail-low-qubit-tricks.md` first.
Read-only: **do not build or run lake in `~/shorecdlp`**. If you need Lean, use a scratch project outside the bench.

## Context

The current entrant (accepted locally) is the upstream 2607.13816 streaming construction at 26 rounds: 3,932 qubits × 374,227,740,666 T
(14,393,374,641 T per round; windows dominated by EEA-based inversion). The human reports that our **ecdlp.ai** point-add submissions have
**formal source-level representations and generated Rust circuits that passed 1,024,000 shots locally**.

Where they are:
- `/mnt/c/code/ecc-formal-toolset`: `routes/gold-*q-*` (1198q … 2820q; e.g. `gold-1240q-fef245d4`, `gold-1337q-877af1c6` with
  server acceptance, `gold-1367q-762f4fcc` with ecdlp submission), `routes/ecdlp-1626q-*`, `routes/ecdlp-1669q-f8`, `formal/{lean,lean429,z3,tla,pantograph}`,
  `docs/gold-descending/`, `AGENTS.md`, `README.md`, and `.claude/worktrees/gold-descent-progress-*/` (notes about 1,024k audits and formal derivations).
- `/mnt/c/code/ecdlp-point-add`: `dist/submission-note.md` + `submission-metadata.json` (1,240 qubits, 2,114,708 emitted CCX+CCZ, 1,974,706 mean
  Toffoli, 1,024,000-shot audit clean; states "still an approximate route; fixed-width guards leave explicitly bounded bad events"), `results.tsv`.
- `/mnt/c/code/secp256k1-point-add-spooky/.workspace/routes/ecdlp-gold-leapfrog-v1` (Gold epoch-11 source/generator/receipts).

## Questions

1. **Inventory.** For each Gold/ecdlp route, give: qubits, emitted (worst-case) CCX+CCZ, mean Toffoli, shots passed, exact or approximate, and
   which formal artifacts exist (what each Lean/Z3/TLA file actually proves, which axioms it uses, and the Lean version). Is there a fully **exact**
   route (no bounded bad events)? If not, what are the bad events, how are their probabilities bounded, and is that bound itself proved?
2. **Formal representation → Lean `Straight`.** The bench needs a data-only straight-line program over X/H/CX/CCX/P/measure-reset with
   `whenBit`/`recordGate` controls (`ShorECDLP/Challenge/StraightLine.lean`, `Template.lean`). Design a generator from the Gold source description
   (the same input that generates the Rust) to Lean `Straight` terms, plus a proof strategy that a kernel can check at this size (~2M nonlinear
   gates per point add): which properties are structural (per-cell lemmas + induction over the source's loop structure) and which would need
   evaluation. Consider proof term size and leanchecker replay limits (the prior P3 artifact hit deep recursion).
3. **Where it plugs in.** (a) As the point-add inside the streaming windows (quantum + table-selected point: what would have to change, since
   Gold adds a *classical* point); (b) as the controlled classical-constant add in a semiclassical one-control-qubit Shor (brief 06 also prices this:
   coordinate with `docs/ECDSAFAIL-TRICKS.md` if it exists). For each, estimate worst-case T-model per round, qubits, rounds and Q×T,
   and how approximate bad events would enter the 99 % success proof (bench `Window/StreamInterference.lean` and related coherent-error lemmas).
4. **Recommendation.** Is a Gold-derived certified entrant realistic, and on what timeline? What is the smallest milestone that proves the
   pipeline end to end (e.g. one exact Gold cell or block lowered to `Straight` with a kernel-checked run/count theorem)?

## Output

`docs/ECDLP-AI-GOLD.md` with the inventory table, generator design, plug-in estimates and recommendation; calculators in `workspace/`; and a LOG line.
Cite paths for every claim; mark guesses as guesses.
