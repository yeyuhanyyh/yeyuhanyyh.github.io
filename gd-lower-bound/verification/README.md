# Rigorous certificate for the scalar inequality

The script [`certify_j_arb.py`](certify_j_arb.py) proves, with directed
outward rounding,

\[
J\!\left(\frac{3171}{5000},\frac{2253}{5000}\right)<0.
\]

It uses `python-flint==0.9.0`, whose `arb` type implements ball arithmetic
backed by Arb. Install and run from the project root:

```text
python -m pip install -r verification/requirements.txt
python verification/certify_j_arb.py --cells 65536 --dps 80
```

The certified run on August 23, 2026 returned

```text
python-flint version: 0.9.0
python-flint Arb precision: 80 decimal digits
interval cells on [0,1/2]: 65536
J enclosure: [-7.42553977089029813385804616530e-5 +/- 2.31e-5]
upper endpoint enclosure: [-5.12188027981393843391214930136e-5 +/- 2.42e-35]
CERTIFIED: J(3171/5000,2253/5000) < -1/20000 < 0
```

## Why this is rigorous

For fixed positive `w,z`, the maximizer defining
\(\Gamma_\lambda(w,z)\) is uniquely parametrized by \(\tau>0\):

\[
X_w(\tau)=\frac{2\tau}{1+\sqrt{1+4\tau/w}},\qquad
A_w(\tau)=w+X_w(\tau),
\]

\[
\frac1{2\tau}+\frac1{A_w(\tau)+A_z(\tau)}=\lambda,
\]

and

\[
\Gamma_\lambda(w,z)
=\log\!\left[\tau\left(\frac1{A_w(\tau)}+
\frac1{A_z(\tau)}\right)\right]
-\lambda\bigl(X_w(\tau)+X_z(\tau)\bigr).
\]

On every interval cell in \(t\), Arb encloses both profile coordinates,
the unique root \(\tau\), and the displayed formula for \(\Gamma_\lambda\).
The root equation is strictly decreasing in \(\tau,w,z\), so sign-verified
mixed-corner brackets contain the optimizer throughout the cell. The first
cell touches \(t=0\); it is bounded by coordinatewise monotonicity:

\[
\Gamma_\lambda(W_\alpha(t),W_\alpha(1-t))
\le \Gamma_\lambda(W_\alpha(h),\alpha),\qquad 0<t\le h.
\]

Summing cell width times the Arb range produces a rigorous enclosure of the
integral and hence of \(J\). Ordinary IEEE double precision appears only in
the generation of candidate root brackets. Those guesses have no logical
role until Arb verifies the required strict signs; a failed sign test expands
the bracket or aborts.

By contrast, the value
\(J\approx-7.4257915942\times10^{-5}\) obtained from high-precision floating
quadrature is useful as a numerical check but is **not** itself a proof.
