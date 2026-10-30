# Bernstein--Yang divsteps milestone 1

Brief 24, 2026-10-29. Exact arithmetic is in
`workspace/divstep_m1.py`; checked Lean is in
`workspace/DivstepMath.lean`.

## Verdict

**Milestone 1 does not pass. No 256-bit termination bound is certified in
Lean, and the n=8 circuit is an exact truth-table baseline rather than the
required scalable divstep cell.** Do not open an Entrant or stack patch.

What is kernel checked:

- the selected half-delta recurrence, with `delta2 = 2δ`, initial `delta2=1`,
  and updates `2-delta2` / `2+delta2`;
- absorbing fixed-horizon padding at `g=0`;
- preservation of odd `f`;
- the scaled transition-matrix invariant
  `2^t [f,g]^T = [[a,b],[c,d]] [f0,g0]^T` for every step and walk;
- the terminal Bezout row, conditional on termination;
- `p < 0x101c…fec2`, the numerical threshold in the external 590-step
  safegcd-bounds receipt;
- exhaustive n=8 termination in 19 steps by kernel `decide`; 18 is impossible,
  witnessed by `(f,g)=(237,235)`;
- a literal `Straight` builder for a 16-input truth-table oracle, plus exact
  constructor-derived counts: 950,272 CCX forward and 1,900,544 for the
  forward circuit followed by its explicit adjoint.

What is not proved:

- the 590-step convex-hull implication in Lean (nor the 724-step classic
  fallback);
- `f=±gcd` at the 256-bit horizon and the final modular-inverse theorem;
- a semantic refinement theorem from the n=8 oracle circuit to the divstep
  model, a formal 57-wire support theorem, and scratch-clean forward theorem;
- a scalable per-tick circuit, the 340-lane packed envelope, exact replay, or
  the 414,770-CCX wrapper receipt.

The conditional BY590 projection therefore remains exactly the Brief 23
screen, not a candidate:

```text
952 × 1,367,811,724 = 1,302,156,761,248
change vs 7,259,679,541,664 = -82.063164720%
```

## 1. Recurrence selected

The source half-delta algorithm starts at `δ=1/2`. Lean avoids fractions by
storing `delta2=2δ`:

```text
g = 0:                  state is unchanged
g even:                 (delta2+2, f,       g/2)
g odd, delta2 > 0:      (2-delta2, g,       (g-f)/2)
g odd, delta2 <= 0:     (delta2+2, f,       (g+f)/2)
```

The explicit absorbing branch is a circuit requirement, not just a
termination convenience: padding must preserve the matrix/transcript state
needed by the reverse walk.

For the scaled matrix, the three updates are:

```text
even:       [[a,b],[c,d]] -> [[2a,2b],[c,d]]
odd/swap:   [[a,b],[c,d]] -> [[2c,2d],[c-a,d-b]]
odd/add:    [[a,b],[c,d]] -> [[2a,2b],[c+a,d+b]]
```

Lean proves these identities for arbitrary integer inputs and any walk length.
At a terminal coprime state with `f=±1`, coefficient `b` decodes the inverse as

```text
g0^-1 = b * f * (2^ticks)^-1 mod f0.
```

The Python audit checks that formula for every coprime n=8 input. The Lean
file currently proves the preceding integer Bezout identity, not this modular
corollary.

## 2. Why 590 was not certified

The later safegcd-bounds development does contain Coq statements for 590
half-delta steps and 724 classic steps. Its 590 theorem covers

```text
M = 0x101c840faed222b9ef3bfe933011b277f84ee3d3f6dc8b496d8cd75b8315afec2
  = 116598219975581070071883298065196158969310383137833836574946009125721210552002
```

and secp256k1's `p` is smaller by

```text
806130738264874648312313056508251116040398472193272535488425117812375880339.
```

However, the final external lemma is closed with
`vm_cast_no_check (refl_equal true)`, after a documented roughly 2.5-day hull
computation. That is useful provenance, but it is not the requested
Lean-kernel replay and cannot be copied into Entrant evidence. The analytic
generic proof in `genproofhd.md` replaces the one-off run with a large
algebraic convex hull involving dyadic/algebraic coordinates; porting and
checking those inclusions is the remaining Part A project.

The older 742 number in Brief 23 is the direct Theorem 11.2-style sensitivity
formula. The later computational Coq development tightens the classic
256-bit receipt to 724. Neither is certified by this Lean work.

Conditional packed projections at the unchanged unproved `W=340`, `H=11`,
`Q=952` profile are:

| Horizon | CCX/wrapper | Total T | Q×T | vs leader |
|---:|---:|---:|---:|---:|
| 590 | 414,770 | 1,367,811,724 | 1,302,156,761,248 | −82.063164720% |
| 724 | 508,972 | 1,411,521,452 | 1,343,768,422,304 | −81.489976044% |
| 742 | 521,626 | 1,417,392,908 | 1,349,358,048,416 | −81.412980550% |

All three rows are screens because width, lowering, replay, and the Lean
termination theorem are absent.

## 3. Exact n=8 results

Kernel enumeration covers all 16,384 pairs with odd `f<256` and `0≤g<f`.
The sharp horizon is 19. The independent Python audit also finds:

| Quantity | Exact value |
|---|---:|
| admissible pairs | 16,384 |
| coprime nonzero pairs | 13,230 |
| maximum steps | 19 |
| witness needing 19 | `(237,235)` |
| maximum `|f|` or `|g|` before absorption | 255 |
| signed value width | 9 bits |
| maximum absolute scaled matrix entry | 1,874 |
| signed matrix width | 12 bits |

### Circuit baseline

The emitted circuit is a fixed, data-independent truth-table oracle. It keeps
the 16 input bits and writes the 19-step terminal signed `f` (9 bits), scaled
matrix coefficient `b` (12 bits), and actual tick count (5 bits) into clean
output wires. Each admissible row computes a 16-bit equality flag with the
bench's clean v-chain, fans it out with Clifford CNOTs, and uncomputes it.

```text
input                 16 wires
output                26 wires
equality flag          1 wire
clean v-chain path    14 wires
support               57 wires (by construction; theorem pending)

CCX per row           2 × (2×16-3) = 58
forward CCX           16,384 × 58 = 950,272
forward+adjoint CCX   1,900,544
```

Only `X`, `CX`, and `CCX` literals are emitted, and `n8ForwardStraight` /
`n8ReverseStraight` are genuine challenge `Straight` values. This is not the
requested sequential divstep implementation: it scales as

```text
rows(n) = 2^(2n-2)
CCX_forward(n) = 2^(2n-2) × (8n-6).
```

At n=256 that is `2042 × 2^510` CCX before the reverse and cannot be compared
as a plausible replacement for the 414,770-CCX screen. Its value is as an
exact small-width lowering baseline and as a check on the model/receipt
interfaces.

## 4. Next proof gate

The next useful work is narrow and proof-first:

1. port the safegcd-bounds hull state/checker to compact Lean data;
2. replace the external VM computation by a chunked certificate whose local
   transitions and final emptiness reduce under kernel `decide` in practical
   time;
3. connect that certificate to `TerminatesBy 590`, gcd preservation, and the
   modular inverse corollary already exposed by the matrix invariant;
4. only then build a sequential n=8 add/swap/halve cell and prove its oracle
   semantics, support, scratch cleanup, and exact receipt.

Do not extrapolate the truth-table circuit into C7b's gate screen, and do not
claim the external Coq theorem as Lean evidence.

Primary sources: [Bernstein--Yang safegcd paper](https://gcd.cr.yp.to/safegcd-20190413.pdf),
[safegcd-bounds and its Coq developments](https://github.com/sipa/safegcd-bounds),
and [libsecp256k1's implementation explanation](https://github.com/bitcoin-core/secp256k1/blob/master/doc/safegcd_implementation.md).
