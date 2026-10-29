# Brief 01 — related-work survey: what transfers from our spooky point-add research

Read `AGENTS.md` and `docs/CHALLENGE.md` (in the lab, your cwd) first.

## Goal

We have prior research at `/mnt/c/code/secp256k1-point-add-spooky` (a repo; start with its `AGENTS.md`,
`README.md`, `docs/`, `research/`, `frontier/`, `formal/`, `work-notes/`, `.workspace/routes/`) and related
build dirs in WSL home: `~/sub870-build`, `~/spooky-build`, `~/r21-lean`. That work optimizes a low-qubit
secp256k1 **point-addition** circuit (Leapfrog / ecdsa.fail, ~1,234 qubits, Q×T < 1e9 per point add), using
spooky pebbling, Lean/Z3/TLA+ obligations, and a `sub870-v1` route.

The current challenge (bench: `~/shorecdlp`) needs a **full Shor ECDLP circuit with a Lean 4 proof** of
≥ 99 % success, scored as qubits × T-model (CCX = 7, P = 1). The shipped entrant has 206,642 qubits × 3.55e14 T.
arXiv:2607.13816 (partially formalized in bench `ShorECDLP/Submission/2607_13816`) claims 854 qubits × 8.0e11 T.

Find everything in the prior work that can be **reused, ported or generalized** here:
1. Circuit constructions: point add / doubling, modular mult/inverse/division, adders, lookup tables,
   windowing, low-qubit layouts, measurement-based uncomputation (spooky/X-basis measure + phase repair).
   For each, estimate the qubit and T-model cost in THIS challenge's cost model.
2. Lean proofs: any existing Lean that proves correctness or resource bounds of reversible arithmetic.
   Note the Lean/Mathlib version compatibility with the bench (`lean-toolchain`: v4.28.0) and how much
   it would take to state it against the bench's `Straight` program / `Framework` semantics.
3. Process and tooling worth copying into this lab: frontier maps, claim/evidence models, schedule IR,
   generators, test harnesses, agent orchestration docs.
4. Relationship to 2607.13816: does `sub870` implement or extend that paper? What would carry over to
   finishing the bench's `Submission/2607_13816` migration inside `Entrant/`?

Read-only on the prior work and the bench. Do not modify either.

## Output

- `docs/RELATED-WORK.md` in the lab: a ranked table (item, location, what it gives, cost estimate here,
  porting effort S/M/L/XL, confidence), followed by a section per top-5 item with concrete file paths and a porting sketch.
- One-line summary appended to `work-notes/LOG.md`.
- Update the Next-up list in `work-notes/HANDOFF.md` if the findings change priorities.

Done when `docs/RELATED-WORK.md` lets a fresh agent pick the most promising transfer without
re-reading the prior repo. Cite paths for every claim. Mark guesses as guesses.
