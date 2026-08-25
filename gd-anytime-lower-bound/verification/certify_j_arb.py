#!/usr/bin/env python3
"""Rigorous Arb certificate for J(3171/5000, 2253/5000) < 0.

This script uses python-flint's ``arb`` balls.  Every arithmetic operation,
elementary function, optimizer enclosure, and integral enclosure is performed
with directed outward rounding.  Ordinary double precision is used only to
*guess* root brackets; every proposed bracket is subsequently verified by
Arb sign tests.

The integral is enclosed by interval Riemann sums.  On each t-cell we enclose
the unique optimizer tau of

    1/(2 tau) + 1/(A_w(tau) + A_z(tau)) = lambda,

where A_w(tau) = (w + sqrt(w^2 + 4 w tau))/2.  Substituting this optimizer,

    Gamma_lambda(w,z)
      = log(tau (A_w+A_z)/(A_w A_z))
        - lambda (A_w+A_z-w-z).

The first cell, which touches t=0, is bounded using coordinatewise
monotonicity of Gamma:

    Gamma(W(t), W(1-t)) <= Gamma(W(h), alpha),  0 <= t <= h.

Run, for example:

    python verification/certify_j_arb.py --cells 65536 --dps 80

The process exits successfully only if the resulting Arb upper endpoint is
strictly negative.
"""

from __future__ import annotations

import argparse
import math
import sys
import time
from fractions import Fraction

import flint
from flint import arb, ctx


ALPHA_Q = Fraction(3171, 5000)
LAMBDA_Q = Fraction(2253, 5000)


def qarb(x: Fraction | int) -> arb:
    """An Arb enclosure of an exact rational."""
    if isinstance(x, int):
        return arb(x)
    return arb(f"{x.numerator}/{x.denominator}")


def hull_rationals(lo: Fraction, hi: Fraction) -> arb:
    """Return an Arb ball containing the exact rational interval [lo, hi]."""
    if not lo <= hi:
        raise ValueError("invalid interval")
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    return arb(f"{mid.numerator}/{mid.denominator}",
               f"{rad.numerator}/{rad.denominator}")


def float_fraction(x: float) -> Fraction:
    """Exact rational represented by Python's shortest decimal for x."""
    return Fraction(repr(float(x)))


def interval_from_floats(lo: float, hi: float) -> arb:
    return hull_rationals(float_fraction(lo), float_fraction(hi))


def W(t: arb, alpha: arb) -> arb:
    """W_alpha(t) = alpha t^(-1-alpha), for a positive Arb interval t."""
    return alpha * (-(arb(1) + alpha) * t.log()).exp()


def X(weight: arb, tau: arb) -> arb:
    """Stable form of (sqrt(w^2+4*w*tau)-w)/2."""
    return 2 * tau / ((1 + 4 * tau / weight).sqrt() + 1)


def A(weight: arb, tau: arb) -> arb:
    return weight + X(weight, tau)


def root_equation(tau: arb, w: arb, z: arb, lam: arb) -> arb:
    aw = A(w, tau)
    az = A(z, tau)
    return 1 / (2 * tau) + 1 / (aw + az) - lam


def root_equation_float(tau: float, w: float, z: float, lam: float) -> float:
    aw = 0.5 * (w + math.sqrt(w * w + 4.0 * w * tau))
    az = 0.5 * (z + math.sqrt(z * z + 4.0 * z * tau))
    return 0.5 / tau + 1.0 / (aw + az) - lam


def root_float(w: float, z: float, lam: float) -> float:
    """Non-rigorous root guess (never used without a later Arb sign test)."""
    lo = 0.5 / lam
    hi = max(2.0 * lo, 2.0)
    while root_equation_float(hi, w, z, lam) > 0.0:
        hi *= 2.0
    # Monotone bisection is stable even for very large w.
    for _ in range(70):
        mid = 0.5 * (lo + hi)
        if root_equation_float(mid, w, z, lam) > 0.0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def verified_lower_root_bound(w_hi: arb, z_hi: arb, lam: arb,
                              lam_float: float) -> Fraction:
    """L with L < tau_*(w_hi,z_hi), certified by F(L)>0."""
    guess = root_float(float(w_hi), float(z_hi), lam_float)
    rel = 2.0e-12
    floor = 0.5 / lam_float
    for _ in range(30):
        candidate = max(floor * (1.0 + 1.0e-15), guess * (1.0 - rel))
        cq = float_fraction(candidate)
        if root_equation(qarb(cq), w_hi, z_hi, lam) > 0:
            return cq
        rel *= 4.0
    raise ArithmeticError("could not certify lower optimizer bound")


def verified_upper_root_bound(w_lo: arb, z_lo: arb, lam: arb,
                              lam_float: float) -> Fraction:
    """U with U > tau_*(w_lo,z_lo), certified by F(U)<0."""
    guess = root_float(float(w_lo), float(z_lo), lam_float)
    rel = 2.0e-12
    for _ in range(30):
        candidate = guess * (1.0 + rel)
        cq = float_fraction(candidate)
        if root_equation(qarb(cq), w_lo, z_lo, lam) < 0:
            return cq
        rel *= 4.0
    raise ArithmeticError("could not certify upper optimizer bound")


def gamma_from_boxes(w: arb, z: arb, tau: arb, lam: arb) -> arb:
    """Natural interval extension of Gamma at an enclosed optimizer tau."""
    x = X(w, tau)
    y = X(z, tau)
    aw = w + x
    az = z + y
    # tau*(A+B)/(A*B) = tau*(1/A+1/B).  Together with x,y this
    # removes two severe interval cancellations near t=0.
    return (tau * (1 / aw + 1 / az)).log() - lam * (x + y)


def gamma_box(tbox: arb, alpha: arb, lam: arb, lam_float: float) -> arb:
    """Enclose Gamma(W(t),W(1-t)) for all t in tbox."""
    wbox = W(tbox, alpha)
    zbox = W(arb(1) - tbox, alpha)

    # F decreases in tau and in each of w,z.  Hence the optimizer is
    # decreasing in w,z.  The following mixed-corner roots enclose every
    # optimizer over the whole (wbox,zbox) rectangle.
    w_lo, w_hi = wbox.lower(), wbox.upper()
    z_lo, z_hi = zbox.lower(), zbox.upper()
    tau_lo = verified_lower_root_bound(w_hi, z_hi, lam, lam_float)
    tau_hi = verified_upper_root_bound(w_lo, z_lo, lam, lam_float)
    taubox = hull_rationals(tau_lo, tau_hi)
    return gamma_from_boxes(wbox, zbox, taubox, lam)


def gamma_point(w: arb, z: arb, lam: arb, lam_float: float) -> arb:
    """Enclose Gamma(w,z) for point balls w,z."""
    tau_lo = verified_lower_root_bound(w.upper(), z.upper(), lam, lam_float)
    tau_hi = verified_upper_root_bound(w.lower(), z.lower(), lam, lam_float)
    return gamma_from_boxes(w, z, hull_rationals(tau_lo, tau_hi), lam)


def certify(cells: int, dps: int, progress: bool = False) -> arb:
    if cells < 2:
        raise ValueError("--cells must be at least 2")
    ctx.dps = dps
    alpha = qarb(ALPHA_Q)
    lam = qarb(LAMBDA_Q)
    lam_float = float(LAMBDA_Q)
    hq = Fraction(1, 2 * cells)  # cells partition [0,1/2]
    h = qarb(hq)

    # The cell [0,h] is handled without evaluating W at zero.
    first_upper = gamma_point(W(h, alpha), alpha, lam, lam_float).upper()
    integral = h * first_upper

    started = time.perf_counter()
    for i in range(1, cells):
        lo = hq * i
        hi = hq * (i + 1)
        tbox = hull_rationals(lo, hi)
        integral += h * gamma_box(tbox, alpha, lam, lam_float)
        if progress and (i % max(1, cells // 20) == 0):
            elapsed = time.perf_counter() - started
            print(f"  {100*i/cells:5.1f}%  ({elapsed:.1f}s)", file=sys.stderr)

    return 2 * lam + 2 * integral


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cells", type=int, default=65536,
                        help="number of interval cells on [0,1/2] (default: 65536)")
    parser.add_argument("--dps", type=int, default=80,
                        help="Arb working precision in decimal digits (default: 80)")
    parser.add_argument("--progress", action="store_true")
    args = parser.parse_args()

    started = time.perf_counter()
    result = certify(args.cells, args.dps, args.progress)
    elapsed = time.perf_counter() - started
    print(f"python-flint version: {flint.__version__}")
    print(f"python-flint Arb precision: {args.dps} decimal digits")
    print(f"interval cells on [0,1/2]: {args.cells}")
    print(f"J enclosure: {result.str(30, more=True)}")
    print(f"upper endpoint enclosure: {result.upper().str(30, more=True)}")
    print(f"elapsed seconds: {elapsed:.3f}")
    clean_bound = qarb(Fraction(-1, 20000))
    if result < clean_bound:
        print("CERTIFIED: J(3171/5000,2253/5000) < -1/20000 < 0")
        return 0
    if result < 0:
        print("CERTIFIED: J(3171/5000,2253/5000) < 0")
        return 0
    print("NOT CERTIFIED: increase --cells and/or --dps", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
