# Half-delta divstep iteration bound (Brief 25)

## Verdict

**No unconditional 256-bit iteration bound was certified.** In particular,
this brief does not claim either 590 or 742. The exact remaining blocker is
the proposition `ShorECDLP.DivstepBound.Has256TrianglePotential` in
`workspace/DivstepBound.lean`: a finite rational polyhedral potential for the
256-bit initial triangle, dominating `|g|` and contracting by `25/32` at every
nonterminal half-delta step.

What is kernel checked is the complete implication from that compact local
certificate to the requested 742-step theorem:

```lean
theorem halfDelta_terminates_742_of_certificate
    (hcert : Has256TrianglePotential) :
  ∀ f0 g0 : Int, Odd f0 → 0 ≤ g0 → g0 ≤ f0 →
    f0 < (2 : Int) ^ 256 →
    (walk 742 (init f0 g0)).g = 0
```

The same file unconditionally proves that every step preserves all common
divisors, hence a terminal state satisfies
`|f| = gcd(f0,g0)`. It repeats and checks the scaled transition-matrix
invariant and proves that, for coprime inputs,

```text
(b*f)*g0 = 2^ticks  (mod f0).
```

For any public `u` satisfying `u*2^ticks = 1 (mod f0)`, Lean proves
`u*(b*f)*g0 = 1 (mod f0)`. Lean also proves that such a `u` exists because
`f0` is odd, and packages the result as `terminal_inverse_exists`; this is the
ordinary modular inverse interface needed for secp256k1.

Check command and receipt:

```text
BENCH=/home/gitzard/shorecdlp-c formal-tools/check.sh workspace/DivstepBound.lean
rc=0 elapsed=2s
axioms: propext, Classical.choice, Quot.sound
```

The observed process peak was about 2.03 GB RSS. There is no `sorry`, `admit`,
`axiom`, `opaque`, `unsafe`, `partial`, `native_decide`, `bv_decide`,
`Lean.ofReduceBool`, or large-object `decide` in this source.

## Recurrence and the 742 mismatch

The selected recurrence is exactly Brief 24's **half-delta** variant. Lean
stores `delta2 = 2*delta`, starts with `delta2 = 1` (`delta = 1/2`), and uses

```text
g = 0:                 unchanged (absorbing padding)
g even:                (delta2+2, f, (g/2))
g odd, delta2 > 0:     (2-delta2, g, (g-f)/2)
g odd, delta2 <= 0:    (delta2+2, f, (g+f)/2).
```

Bernstein--Yang Theorem 11.2 proves the familiar
`floor((49*d+57)/17) = 741` sufficient count at `d=256` (the older project
screen rounded this to 742), but it starts the classic recurrence at
`delta=1`. It cannot be applied to the chosen `delta=1/2` walk merely because
the branch formulas look similar. The later safegcd-bounds half-delta result
is the relevant source and gives the stronger 590 threshold, but its final
Coq emptiness receipt is closed by `vm_cast_no_check` after a very large hull
computation. That receipt remains inadmissible here.

## Kernel-checked progress

`workspace/DivstepBound.lean` proves:

1. absorption of `g=0` and propagation of nontermination backwards through a
   fixed walk;
2. odd-`f` preservation;
3. equivalence of common divisors for all three branches, including the
   nontrivial cancellation of 2 using oddness;
4. gcd preservation for every walk and the explicit disjunction
   `f_terminal = gcd(f0,g0) ∨ f_terminal = -gcd(f0,g0)`;
5. the scaled transition-matrix invariant
   `2^ticks [f,g]^T = [[a,b],[c,d]][f0,g0]^T`;
6. the scaled and unscaled modular-inverse congruences;
7. the generic potential induction; and
8. exact rational arithmetic showing
   `(25/32)^742 * 4 * 2^256 < 1`.

The potential interface is:

```lean
structure PotentialCertificate (P : Int → Int → Int → Rat) : Prop where
  nonneg      : 0 ≤ P delta2 f g
  dominatesG  : |g| ≤ P delta2 f g
  contracts   : g != 0 → 32*P(step(delta2,f,g)) ≤ 25*P(delta2,f,g)
```

Together with `P(1,f,g) ≤ 4*2^256` on
`0 ≤ g ≤ f < 2^256`, these local inequalities imply termination. The slack is
intentional: `25/32 = 0.78125` is substantially weaker than the published
half-delta asymptotic contraction near `0.74015`, so a rational outer
polytope need not reproduce the exact algebraic stable hull.

## Exact blocker and next experiment

The missing theorem is precisely:

```lean
Has256TrianglePotential
```

with a concrete `P`. A useful next attempt is to rationally outer-approximate
the published stable half-delta hull at contraction `25/32`, encode the
result as a short list of rational half-planes, and reduce `contracts` to
kernel-friendly vertex/face inequalities. The certificate should be split by
the two central half-delta states and the finite boundary cases; the affine
tails for large positive/negative delta should be discharged symbolically.
This avoids replaying 742 growing AVL convex hulls and isolates any finite
computation into small `norm_num` or kernel `decide` checks.

## Conditional score impact

No score row is certified because the bound witness, fixed width, replay, and
circuit receipt are still missing. At the existing unproved `W=340`, `Q=952`
screen, a 742-step wrapper costs 521,626 CCX and projects

```text
952 × 1,417,392,908 = 1,349,358,048,416
change vs 7,259,679,541,664 = -81.412980550%
```

For comparison, the still-unreplayed 590-step hull screen is
`952 × 1,367,811,724 = 1,302,156,761,248` (`-82.063164720%`). These remain
screens, not candidates. No bench file, Entrant, stack patch, score, snapshot,
submission, or commit was made.

Primary sources: Bernstein and Yang, *Fast constant-time gcd computation and
modular inversion*, especially Theorem 11.2 and Appendices F--G; and
`sipa/safegcd-bounds`, especially `genproofhd.md` and the half-delta Coq
development.
