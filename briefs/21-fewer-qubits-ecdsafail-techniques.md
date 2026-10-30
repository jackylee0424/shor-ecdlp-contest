# Brief 21 — trade gates for fewer qubits: apply ecdsa.fail low-qubit techniques to the leader's 855 wires (analysis first)

Read `AGENTS.md`, `docs/LEVERS.md` (rows B, G), `docs/QUBITS-FOR-GATES.md` (the opposite direction, adding wires), `docs/ECDSAFAIL-TRICKS.md`,
`docs/ECDSAFAIL-855.md`, `docs/SPOOKY-ON-09.md` and `docs/RELATED-WORK.md`. Submissions are **on hold**; this is research.

## Baseline

Leader **spariev `f7419f1` (bench `5d39a5f`): 855 × 11,512,613,384 = 9,843,284,443,320.** Single trial; 263-bit left axis; 224-bit physical right axis rounded to a 203-bit `wrappedShift` word;
1 direct + 30 corrected windows; temporary-AND compiler (one reusable ancilla); borrowed arithmetic flag on the lookup root 836 (so 854 core wires + 1 ancilla).
**Removing one wire is worth it iff the T increase is < 11,512,613,384/855 ≈ 13.46M T** (more precisely ΔT/T < 1/855 per wire).

Bench: `~/shorecdlp` is yours (reset it to `5d39a5f`: `git fetch origin; git reset --hard 5d39a5f; git clean -fd -- ShorECDLP/Submission/Entrant`). Read-only analysis plus Lean scratch
via `BENCH=/home/gitzard/shorecdlp formal-tools/check.sh workspace/Q21*.lean`. Don't touch `~/shorecdlp-c` (brief 20) or `~/shorecdlp-m`.

## Tasks

1. **Wire census of the leader.** Using the support lemmas (`CompleteSupport`, `WindowSupport`, `ArithmeticSupport`, the reset list, and the 854/855 accounting in `f7419f1`), list every
   label group (accumulator x/y/infinity 513, EEA work/rotation/length registers, multiply workspace, Fourier/address/sign bank, lookup path and root, flags, compiler
   ancilla) with **its live intervals across the window schedule**. Find the phase that sets the peak, and which groups are idle there. (The qubit metric is the union of
   labels, so any group that is clean during the peak phase is a sharing candidate.)
2. **ecdsa.fail low-qubit techniques**, mapped onto that census. Sources: `research/ecdsafail-notes/` (660–700q: `dc0f02e`, `9a8bbca`, `a3f9f6a`, `6b478c8`, `55edbc4`, `31abffd`,
   `0ab84d9`, `39a9153`, `f95b5d9`, ours `f0bd623`, `8d916b4`, `8cbf348`; 815–849q: BitWonka `29c8560` `954016d` `73799fc`, odinfree, SnehalRaj, gopikannappan), and our spooky lab
   `/mnt/c/code/secp256k1-point-add-spooky` (lowq-lineage, sub870, spooky theory, lane loans). For each technique (lane loans/borrowing clean or dirty wires, register sharing between
   EEA and multiply, in-place arithmetic, packed cofactor rings, spooky measure-and-recompute, address-bank folding, Fourier bank reuse, ...) say whether it applies **exactly** to
   the leader, which label group it shrinks, by how many wires, and the exact worst-case T it adds (price CCX at 5 under the compiler; measured erasure 0).
3. **Marginal curve:** the best achievable score for each total qubit count from 855 down to ~800, picking the cheapest wires first. Mark the crossover where ΔT per wire exceeds 13.46M.
4. **Recommendation:** the top 1–3 builds as stack patches on `5d39a5f`, with exact projected score and % vs the leader, and the Lean effort (S/M/L/XL).

## Output

`docs/FEWER-QUBITS.md` (verdict first), `workspace/fewer_qubits.py` (exact integers), Lean scratch if useful, a LOG line, and LEVERS B-rows. No submissions or commits.
