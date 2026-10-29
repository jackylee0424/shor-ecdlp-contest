#!/usr/bin/env python3
"""Brief 05: upstream mass formula, numerical diagnostics and round budgets.

Pure Python; no Lean/bench writes. Numerics and proposed bounds are not proofs.
The exact accepted mass depends on d; 16/pi^4 is its existing LOWER bound.
"""
import math
import random
from fractions import Fraction

ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
T_ROUND = 14_393_374_641
Q = 3932


def rounds(p):
    return math.ceil(math.log(.01) / math.log1p(-p))


def sinc_sq(x):
    return 1.0 if x == 0 else (math.sin(math.pi*x)/(math.pi*x))**2


def integrate(f, a, b, steps=20000):
    h = (b-a)/steps
    return h/3*(f(a)+f(b)+sum((4 if i % 2 else 2)*f(a+i*h)
                            for i in range(1, steps)))


def even_moments(r):
    """Exact averages of centered residues^2,^4,^6 for odd r."""
    h = (r-1)//2
    sums = (h*(h+1)*(2*h+1)//6,
            h*(h+1)*(2*h+1)*(3*h*h+3*h-1)//30,
            h*(h+1)*(2*h+1)*(3*h**4+6*h**3-3*h+1)//42)
    return [Fraction(2*s, r**(j+1)) for j, s in zip((2, 4, 6), sums)]


def polynomial_bound(r):
    """Conditional on the stated analytic sinc polynomial minorant.

    Use rational pi brackets with signs chosen for a rigorous arithmetic bound.
    This calculation is exact; the analytic and finite-mixture lemmas need Lean.
    """
    lo, hi = Fraction(31415, 10000), Fraction(31416, 10000)
    m2, m4, m6 = even_moments(r)
    a = 1-hi**2*m2/3+2*lo**4*m4/45-hi**6*m6/315
    # Remove k=0, whose peak product is 1, since the decoder needs k != 0.
    return a, 2*a-1-Fraction(1, r)


def peak_mass(r, bits, k, out):
    n = 1 << bits
    # Integer arithmetic avoids catastrophic cancellation at 256-bit precision.
    rem = (n*k-r*out) % (r*n)
    if 2*rem > r*n:
        rem -= r*n
    if rem == 0:
        return 1.0
    x = rem/r
    return (math.sin(math.pi*x)/(n*math.sin(math.pi*x/n)))**2


def small_exact_mass(r=31, left=5, right=3, d=1):
    """Enumerate the FULL finite accepted event at a small prime analogue."""
    total = 0.0
    for a in range(1 << left):
        khat = ((2*r*a+(1 << left))//(2*(1 << left))) % r
        for b in range(1 << right):
            nums = set()
            for value in ([b, 1 << right] if b == 0 else [b]):
                low = max(0, 2*r*value-r)//(2*(1 << right))
                high = (2*r*value+r)//(2*(1 << right))
                nums.update(range(low, high+1))
            # inverse of zero in ZMod is zero, never a nonzero secret.
            if khat == 0 or (d*khat) % r not in {l % r for l in nums}:
                continue
            total += sum(peak_mass(r, left, k, a)*
                         peak_mass(r, right, (d*k) % r, b)
                         for k in range(r))/r
    return total


def sample_peak_subset(d, samples=50000):
    """Monte Carlo of the guaranteed nearest-pair SUBSET, not full acceptance."""
    rng = random.Random(5)
    vals = []
    for _ in range(samples):
        k = rng.randrange(1, ORDER)
        residues = [((1 << bits)*v) % ORDER
                    for bits, v in ((256, k), (208, d*k % ORDER))]
        delta = [(z if 2*z <= ORDER else z-ORDER)/ORDER for z in residues]
        vals.append(sinc_sq(delta[0])*sinc_sq(delta[1]))
    mean = sum(vals)/samples
    se = math.sqrt(sum((v-mean)**2 for v in vals)/(samples-1)/samples)
    return mean, se


if __name__ == '__main__':
    average = integrate(sinc_sq, -.5, .5)
    a, p = polynomial_bound(ORDER)
    print(f'Existing analytic lower bound: {(1-1/ORDER)*16/math.pi**4:.12f}')
    print(f'Average nearest peak (continuum): {average:.12f}')
    print(f'Independent-phase diagnostic (not uniform in d): {average**2:.12f}')
    print(f'Uniform marginal/product route (continuum): {2*average-1:.12f}')
    print(f'Proposed polynomial marginal >= {float(a):.12f}; pair >= {float(p):.12f}')
    assert p > Fraction(546, 1000)
    print('\np | rounds | T | Q*T (3932 wires)')
    for prob in (.163, 16/math.pi**4, .2, .25, .3, .4, .5, .546, .6, .7, .75):
        r = rounds(prob)
        print(f'{prob:.12f} | {r} | {r*T_ROUND} | {Q*r*T_ROUND}')
    print('\nrightBits | minimum full 16-bit windows | max rounds under candidate cap')
    cap = 56*((1 << 49)+2)
    for bits in (192, 204, 205, 206, 207, 208, 209, 224):
        limit = 2*(ORDER//(1 << bits)+2)
        print(bits, (bits+15)//16, cap//limit, sep=' | ')
    print('\nSmall-prime FULL accepted mass: r=31, n=5, m=3')
    for d in (1, 2, 7, 15, 30):
        print(f'd={d}: {small_exact_mass(d=d):.9f}')
    print('\nsecp256k1 nearest-pair SUBSET Monte Carlo (mean +/- standard error)')
    for d in (1, 1 << 48, ORDER//3, 0x123456789ABCDEF0123456789):
        mean, se = sample_peak_subset(d)
        print(f'd={d}: {mean:.9f} +/- {se:.9f}')
