# 2026-10-29 — dirty-borrowed exact multiplier gate

- **Agent:** Codex
- **Hypothesis:** An exact signed-digit Horner cell with a dirty-borrowed pseudo-Mersenne fold can replace all eight multiply/square calls per corrected window at 855 qubits and cut total T by at least 3%.
- **Starting snapshot:** leader dadon `c6a88fc`; bench `c13a2934fdd7c204e00d91b5429bbdc726c35277` in `/home/gitzard/shorecdlp-m`

## Plan

1. Re-audit the eight physical call boundaries on the single-trial entrant.
2. Reprice the 30-window resource chain, separating the five spacious sites from the three 25-lane sites.
3. Derive an exact fused signed-add/double identity and price every boundary repair with a worst-case count.
4. Mutate the bench and create `stack/30-fast-multiplier/` only if the exact count clears 3%.

## What happened

- `BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/MulClean.lean` passed in 11s. The base change did not alter the site inventory: the three post-forward-EEA calls still expose exactly 25 proved-clean lanes; the other multiply sites expose 68 and the square sites 69.
- The single-trial source has one direct load and 30 corrected windows. Each corrected window makes six Horner calls and two square-ladder calls. Each existing call is exactly `1,110,533 CCX = 7,773,731 T`, decomposed as 255 recurring `(modular add; modular double)` cells of 4,344 CCX plus one terminal 2,813-CCX modular add.
- Therefore 61,200 recurring cells are replaceable. A uniform replacement must be below about 3,268 CCX/cell for a 3% total cut. More generally the strict condition is `5*high + 3*low < 26144.023001 CCX`, where `high` and `low` are the spacious- and tight-site cell costs.
- The read-only ecdsa.fail donor test `cargo test ftprod_roundtrips -- --nocapture` emitted 138,289 / 119,603 / 91,446 Toffolis at pools 76 / 147 / 256. `ftprod_signed_modadd` emitted 547 / 534 / 461 / 353 / 351 at pools 64 / 76 / 147 / 255 / 256. These are not eligible exact counts: the source explicitly truncates the fold at 64 lanes, erases the overflow with only 32 top lanes, and assumes the post-fold high bit outside exceptional boundary bands.
- `workspace/FastMulAlgebra.lean` kernel-checks the exact pseudo-Mersenne identity `2^256 ≡ 2^32+977 (mod p)` and the signed-digit Horner identity. It uses no new axiom or native decision shortcut.
- `workspace/dirtyfold_feasibility.py` derives and tests the exact fused classical skeleton. With `N=2^256`, `c=2^32+977`, raw complemented-add carry `k`, restored raw word `v`, high bit `h`, and rotated word `d`, the needed small signed addend is

  `B = 2*(-1)^s*k*c + h*(c-1)`

  and the canonical answer is `d + B - q*p`, where `q = floor((d+B)/p)` and `q ∈ {-1,0,1}`. Boundary and 20,000 deterministic random pairs passed the integer identity.
- The remaining exact circuit obligation is not merely a Boolean dirty MCX. Computing `q` is a narrow high-prefix/low-threshold test, but after its correction the quotient flag must be erased with no branch-dependent phase. The proved dirty MCX restores arbitrary donors, yet its coherent inverse requires the pre-correction word; measuring the flag requires a phase oracle for the same exact predicate. Reconstructing that predicate needs a full exact word carry/comparison (or a new continuation-aware measured-uncompute theorem). No existing bench theorem supplies the latter.
- Pricing the donor headline while omitting this cleanup would project a 10.605976% cut at 540 CCX/cell, but that is an approximate/non-circuit number. The only completely specified and machine-proved exact cell remains the current 4,344-CCX cell, for a 0% cut. Conditional sensitivity examples are printed by the calculator and are explicitly not circuit claims.

Commands:

```sh
BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/MulClean.lean
BENCH=/home/gitzard/shorecdlp-m formal-tools/check.sh workspace/FastMulAlgebra.lean
python3 workspace/dirtyfold_feasibility.py
CARGO_TARGET_DIR=/tmp/brief16-cargo-target cargo test ftprod_roundtrips -- --nocapture
CARGO_TARGET_DIR=/tmp/brief16-cargo-target cargo test ftprod_signed_modadd -- --nocapture
```

## Result

| Qubits | T-model | Q×T | Proved? | Snapshot |
|---:|---:|---:|:---:|---|
| 855 | 15,365,238,944 | 13,137,279,297,120 | yes (unchanged base) | none; bench untouched |

Patch-alone improvement: **0.000000% achieved**. No candidate was scored, so there is no SCOREBOARD row.

Provenance: retain dadon's and the protected entrant's existing credits. The algorithmic direction is inspired by the ecdsa.fail `modp_ft` lineage; the donor-restoring dirty MCX is from our ecdsa.fail low-qubit work. No donor source was copied into an Entrant.

## Verdict

**Stop at the mandatory exact-count gate.** The single-trial opportunity is large enough conditionally, but no exact 25-lane dirty-fold circuit with restored donors, zero phase garbage and a worst-case count was completed. This is not a lower-bound proof that every exact fast multiplier saves less than 3%; it means the prerequisite exact count was not established, so the gate cannot pass. Creating `stack/30-fast-multiplier/ENABLED` or changing the Entrant would falsely promote the donor's exceptional-state approximation.

C8 can reopen with one of these concrete prerequisites:

- a continuation-aware measured uncompute theorem for the narrow `q` predicate, retaining the pre-correction carry frame until the phase debt is repaid;
- an exact dirty-borrowed variable-word add/compare whose combined cell satisfies `5*high + 3*low < 26144.023001` CCX;
- or a layout change that supplies enough clean carry lanes at the three 25-lane sites while keeping support at 855.

