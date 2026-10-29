#!/usr/bin/env python3
"""Numerics for Brief 14: the *full* wrappedShift accepted event.

This is evidence, not a certificate.  All integer reductions and decoder
rounding are exact.  Floating point is used only for the final trigonometric
evaluation of the exact finite-L phase-estimation peak function.

The accepted set is almost a graph.  If a is the left output and

    h(a) = round(r*a/N),

then a nonzero secret d is in fixedCandidates(a,b) exactly when h(a) != 0
and the residue d*h(a) has an integer representative in the decoder's
half-bin interval for b.  Inverting those inequalities gives one, or very
occasionally two, right bins.  Thus the full mass can be summed over a
rather than over the enormous candidate intervals.
"""

from __future__ import annotations

import argparse
import math
import random
from dataclasses import dataclass


ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
N = 1 << 256
M = 1 << 208


def required_per_round(rounds: int) -> float:
    return 1.0 - 0.01 ** (1.0 / rounds)


def rounded_bin(r: int, size: int, k: int) -> int:
    """Wrapped round(size*k/r), exactly as reducedPeak."""
    return ((2 * size * k + r) // (2 * r)) % size


def decoded_left(r: int, size: int, a: int) -> int:
    """nearestNumerator r bits a, with size=2^bits."""
    return (2 * r * a + size) // (2 * size)


def finite_peak_mass(r: int, size: int, k: int, out: int) -> float:
    """Exact finite-L formula |sin(pi*x)/(L*sin(pi*x/L))|^2.

    x=size*k/r-out.  Reducing only the numerator modulo r avoids losing
    its fractional part when x is enormous (the 208-bit wrong-bin case).
    """
    e = size * k - r * out
    if e == 0:
        return 1.0
    rem = e % r
    if 2 * rem > r:
        rem -= r
    numerator = math.sin(math.pi * (rem / r))
    denominator = size * math.sin(math.pi * (e / (r * size)))
    if denominator == 0.0:
        # The only physical endpoint identity is e=0, handled above.
        return 0.0
    return (numerator / denominator) ** 2


def ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


def accepted_right_bins(r: int, n: int, m: int, d: int, a: int) -> tuple[int, ...]:
    """All physical right bins accepting d for left output a.

    This is the exact inverse of numeratorInterval, including its floored
    lower endpoint and the wrapped b=0 copy of the formal endpoint b=M.
    """
    h = decoded_left(r, n, a)
    if h == 0:
        return ()
    ell = (d * h) % r
    lo = ceil_div(2 * m * ell - r, 2 * r)
    hi = ceil_div(2 * m * (ell + 1) + r, 2 * r) - 1
    bins = set(range(max(0, lo), min(m - 1, hi) + 1))
    endpoint = numerator_interval(r, m, m)
    if ell in endpoint or ell + r in endpoint:
        bins.add(0)
    return tuple(sorted(bins))


def full_character_mass_truncated(
    r: int, n: int, m: int, d: int, k: int, radius: int
) -> float:
    """Accepted mass for latent k, summing cyclic left offsets |j|<=radius."""
    a0 = rounded_bin(r, n, k)
    total = 0.0
    for j in range(-radius, radius + 1):
        a = (a0 + j) % n
        for b in accepted_right_bins(r, n, m, d, a):
            total += finite_peak_mass(r, n, k, a) * finite_peak_mass(
                r, m, (d * k) % r, b
            )
    return total


def nearest_character_mass(r: int, n: int, m: int, d: int, k: int) -> float:
    a = rounded_bin(r, n, k)
    b = rounded_bin(r, m, (d * k) % r)
    return finite_peak_mass(r, n, k, a) * finite_peak_mass(r, m, (d * k) % r, b)


@dataclass(frozen=True)
class Estimate:
    mean: float
    standard_error: float
    samples: int


def estimate(
    d: int,
    samples: int,
    seed: int,
    radius: int | None = None,
    r: int = ORDER,
    n: int = N,
    m: int = M,
) -> Estimate:
    rng = random.Random(seed)
    sum_x = 0.0
    sum_x2 = 0.0
    for _ in range(samples):
        k = rng.randrange(r)
        if radius is None:
            x = nearest_character_mass(r, n, m, d, k)
        else:
            x = full_character_mass_truncated(r, n, m, d, k, radius)
        sum_x += x
        sum_x2 += x * x
    mean = sum_x / samples
    variance = max(0.0, (sum_x2 - samples * mean * mean) / (samples - 1))
    return Estimate(mean, math.sqrt(variance / samples), samples)


def left_tail_bound(radius: int) -> float:
    """Uniform omitted left probability bound for cyclic offsets |j|>J.

    sin(pi*t)>=2t on [0,1/2] gives P(j)<=1/(4(|j|-1/2)^2),
    and comparison with an integral gives the stated bound.
    """
    return 1.0 / (2.0 * (radius - 0.5))


def inner_wrong_right_bound(d: int, radius: int, r: int = ORDER, m: int = M) -> tuple[float, int, int]:
    """Uniform right-axis bound for decoded-character shifts 0<|s|<=J.

    Returns (probability bound, minimizing |s|, minimum circular residue).
    Rounding the shifted character's peak changes its phase by <=1/(2M).
    """
    best_residue = r
    best_s = 0
    for s in range(1, radius + 1):
        z = (d * s) % r
        z = min(z, r - z)
        if z < best_residue:
            best_residue, best_s = z, s
    theta = best_residue / r - 1.0 / (2.0 * m)
    if theta <= 0.0:
        return 1.0, best_s, best_residue
    den = m * math.sin(math.pi * theta)
    return min(1.0, 1.0 / (den * den)), best_s, best_residue


def fib_ratio_secret(r: int = ORDER) -> int:
    """A 256-bit badly-approximable slope, approximately r/phi."""
    a, b = 0, 1
    while b.bit_length() <= 300:
        a, b = b, a + b
    return (r * a) // b


def numerator_interval(r: int, size: int, value: int) -> range:
    lo = max(0, 2 * r * value - r) // (2 * size)
    hi = (2 * r * value + r) // (2 * size)
    return range(lo, hi + 1)


def brute_accepts(r: int, n: int, m: int, d: int, a: int, b: int) -> bool:
    h = decoded_left(r, n, a)
    nums = set(numerator_interval(r, m, b))
    if b == 0:
        nums.update(numerator_interval(r, m, m))
    # In a prime field h^-1=0 iff h=0.  Test the image definition directly.
    return any((ell * pow(h, -1, r)) % r == d % r for ell in nums) if h else False


def small_full_mass(r: int, n: int, m: int, d: int, graph: bool) -> float:
    total = 0.0
    for k in range(r):
        for a in range(n):
            if graph:
                bs = accepted_right_bins(r, n, m, d, a)
            else:
                bs = [b for b in range(m) if brute_accepts(r, n, m, d, a, b)]
            for b in bs:
                total += finite_peak_mass(r, n, k, a) * finite_peak_mass(
                    r, m, (d * k) % r, b
                ) / r
    return total


def search_random(count: int, samples: int, seed: int) -> list[tuple[float, int]]:
    rng = random.Random(seed)
    candidates = [rng.randrange(1, ORDER) for _ in range(count)]
    scored = [(estimate(d, samples, seed + 1).mean, d) for d in candidates]
    return sorted(scored)[:5]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=100_000)
    parser.add_argument("--full-samples", type=int, default=12_000)
    parser.add_argument("--radius", type=int, default=128)
    parser.add_argument("--search", type=int, default=32)
    parser.add_argument("--search-samples", type=int, default=8_000)
    parser.add_argument("--seed", type=int, default=14029)
    args = parser.parse_args()

    print("required p:", " ".join(
        f"{q} rounds={required_per_round(q):.12f}" for q in (5, 4, 3)
    ))
    print("small-prime exact full enumeration (r=31,N=32,M=8)")
    for d in (1, 2, 7, 15, 30):
        direct = small_full_mass(31, 32, 8, d, False)
        graph = small_full_mass(31, 32, 8, d, True)
        assert abs(direct - graph) < 2e-14
        print(f"  d={d:2d}: {graph:.12f} (graph=direct)")

    golden = fib_ratio_secret()
    found = search_random(args.search, args.search_samples, args.seed)
    print("random-d nearest-pair search (coarse):")
    for mass, d in found:
        print(f"  {mass:.9f} d=0x{d:x}")

    cases = [
        ("1", 1, True),
        ("2", 2, True),
        ("17", 17, True),
        ("2^48-1", (1 << 48) - 1, True),
        ("2^48", 1 << 48, True),
        ("2^48+1", (1 << 48) + 1, True),
        ("r-1", ORDER - 1, True),
        ("golden", golden, False),
        ("search-min", found[0][1], False),
    ]
    print(f"full accepted estimates (full uses |j|<={args.radius}; +/- is Monte Carlo SE)")
    for i, (name, d, do_full) in enumerate(cases):
        if do_full:
            e = estimate(d, args.full_samples, args.seed + 10 + i, args.radius)
            suffix = f" tail<={left_tail_bound(args.radius):.3e}"
        else:
            e = estimate(d, args.samples, args.seed + 10 + i)
            wrong, s, residue = inner_wrong_right_bound(d, 8192)
            suffix = (f" nearest; full <= nearest+{left_tail_bound(8192)+wrong:.3e}"
                      f" (min shift s={s}, residue/r={residue/ORDER:.3e})")
        print(f"  {name:10s} {e.mean:.9f} +/- {e.standard_error:.9f}{suffix}")

    # Refine the two candidates relevant to a no-go witness with common settings.
    print("refined no-go witnesses (nearest mass plus deterministic full-mass ceiling)")
    for i, (name, d) in enumerate((('golden', golden), ('search-min', found[0][1]))):
        e = estimate(d, max(args.samples, 400_000), args.seed + 100 + i)
        wrong, s, residue = inner_wrong_right_bound(d, 8192)
        allowance = left_tail_bound(8192) + wrong
        print(f"  {name:10s} nearest={e.mean:.9f} +/- {e.standard_error:.9f}; "
              f"full ceiling estimate={e.mean+allowance:.9f}; allowance={allowance:.3e}; "
              f"min s={s}, residue/r={residue/ORDER:.3e}")


if __name__ == "__main__":
    main()
