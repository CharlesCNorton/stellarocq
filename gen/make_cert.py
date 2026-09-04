"""Emit a Stellarocq certificate from a VMEC wout file.

The certificate states, for a set of full-grid nodes and angles, that the
mu0-scaled ideal-MHD force residual of the equilibrium reconstructed from the
wout coefficients by VMEC's own half-grid rule (fixed in theories/Physics.v)
lies within the claimed per-component bounds: r_s at the node from the
centered differences of its two half points, r_u and r_v at the outer half
point.  Every numeric input is an IEEE double from the wout, emitted exactly
as a dyadic rational m*2^e; the checker encloses the true real arithmetic
with proven-sound interval arithmetic, so a VALID verdict is a theorem about
these exact inputs.

Environment layout per point (must match theories/Physics.v):
  0 s_j | 1 u | 2 v | 3 phip | 4..6 s_{j-1} s_j s_{j+1} | 7..8 s_{j-1/2} s_{j+1/2}
  9..10 iota(h-) iota(h+) | 11..31 am | 32+0..3K-1 R (rows j-1, j, j+1)
  +3K Z | +6K lambda (rows h-, h+)      (K = mnmax)
  32+8K..   scratch slots the checker fills with shared subexpressions

With --cells the certificate instead claims its bounds over cells of angles,
so that a VALID verdict covers the continuum between the sampled angles and
not only the samples. The bounds of a cell certificate are written by the
checker itself:

  python make_cert.py wout_X.nc cell_X.txt --cells --nu 8192
  main --tighten cell_X.txt cert_X.txt
  main cert_X.txt

Usage:  python make_cert.py wout_X.nc cert_X.txt  [--nodes 6] [--nu 8] [--nv 4]
"""

import argparse
import pathlib
import re

import numpy as np

MU0 = 4e-7 * np.pi


def dyadic(x):
    """Exact (mantissa, exponent) with x = m * 2**e, for a finite double."""
    num, den = float(x).as_integer_ratio()
    e = 0
    d = den
    while d > 1:
        d >>= 1
        e -= 1
    m = num
    while m != 0 and m % 2 == 0:
        m //= 2
        e += 1
    if m == 0:
        e = 0
    return m, e


def spline_second_derivatives(xx, yy):
    """The second derivatives of VMEC's cubic spline through (xx, yy).

    This is `spline_cubic.f`: the end derivatives come from a quadratic fit
    through the first and last three knots, and the interior from the
    Numerical Recipes clamped tridiagonal solve.
    """
    n = len(xx)
    c = ((yy[2] - yy[0]) / (xx[2] - xx[0]) - (yy[1] - yy[0]) / (xx[1] - xx[0])) / (
        xx[2] - xx[1]
    )
    yp1 = (yy[1] - yy[0]) / (xx[1] - xx[0]) - c * (xx[1] - xx[0])
    c = (
        (yy[n - 3] - yy[n - 1]) / (xx[n - 3] - xx[n - 1])
        - (yy[n - 2] - yy[n - 1]) / (xx[n - 2] - xx[n - 1])
    ) / (xx[n - 3] - xx[n - 2])
    ypn = (yy[n - 2] - yy[n - 1]) / (xx[n - 2] - xx[n - 1]) - c * (xx[n - 2] - xx[n - 1])
    y2 = np.zeros(n)
    u = np.zeros(n)
    y2[0] = -0.5
    u[0] = (3.0 / (xx[1] - xx[0])) * ((yy[1] - yy[0]) / (xx[1] - xx[0]) - yp1)
    for i in range(1, n - 1):
        sig = (xx[i] - xx[i - 1]) / (xx[i + 1] - xx[i - 1])
        p = sig * y2[i - 1] + 2.0
        y2[i] = (sig - 1.0) / p
        u[i] = (
            6.0
            * (
                (yy[i + 1] - yy[i]) / (xx[i + 1] - xx[i])
                - (yy[i] - yy[i - 1]) / (xx[i] - xx[i - 1])
            )
            / (xx[i + 1] - xx[i - 1])
            - sig * u[i - 1]
        ) / p
    qn = 0.5
    un = (3.0 / (xx[n - 1] - xx[n - 2])) * (
        ypn - (yy[n - 1] - yy[n - 2]) / (xx[n - 1] - xx[n - 2])
    )
    y2[n - 1] = (un - qn * u[n - 2]) / (qn * y2[n - 2] + 1.0)
    for k in range(n - 2, -1, -1):
        y2[k] = y2[k] * y2[k + 1] + u[k]
    return y2


def spline_eval(xx, yy, y2, x):
    """The spline at x."""
    x = min(max(x, xx[0]), xx[-1])
    k = int(np.clip(np.searchsorted(xx, x) - 1, 0, len(xx) - 2))
    h = xx[k + 1] - xx[k]
    a = (xx[k + 1] - x) / h
    b = (x - xx[k]) / h
    return a * yy[k] + b * yy[k + 1] + ((a**3 - a) * y2[k] + (b**3 - b) * y2[k + 1]) * h * h / 6.0


def spline_piece(xx, yy, y2, x):
    """The cubic of the piece containing x, as (knot, a0, a1, a2, a3) with
    the value a0 + a1 t + a2 t^2 + a3 t^3 at t = x - knot."""
    k = int(np.clip(np.searchsorted(xx, x) - 1, 0, len(xx) - 2))
    h = xx[k + 1] - xx[k]
    c0 = y2[k] * h * h / 6.0
    c1 = y2[k + 1] * h * h / 6.0
    # in the normalized coordinate q = t / h
    q0 = yy[k]
    q1 = (yy[k + 1] - yy[k]) - 2.0 * c0 - c1
    q2 = 3.0 * c0
    q3 = c1 - c0
    return xx[k], q0, q1 / h, q2 / (h * h), q3 / (h * h * h)


def akima_piece(xx, yy, x):
    """The cubic of the Akima piece containing x, as (knot, a, b, c, d) with
    the value a + t (b + t (c + d t)) at t = x - knot.

    This mirrors `BuildAkimaCoeffs`: four phantom knots, the edge values by a
    quadratic fit at each end, and the Akima weights for the slopes.
    """
    iv = len(xx)
    if iv < 4:
        msg = "an akima_spline pressure needs at least four knots"
        raise SystemExit(msg)
    o = 1
    sz = iv + 4
    X = np.zeros(sz)
    Y = np.zeros(sz)
    M = np.zeros(sz)
    DM = np.zeros(sz)
    P = np.zeros(sz)
    Q = np.zeros(sz)
    T = np.zeros(sz)
    for i in range(1, iv + 1):
        X[i + o] = xx[i - 1]
        Y[i + o] = yy[i - 1]
    X[-1 + o] = 2 * X[1 + o] - X[3 + o]
    X[0 + o] = X[1 + o] + X[2 + o] - X[3 + o]
    X[iv + 2 + o] = 2 * X[iv + o] - X[iv - 2 + o]
    X[iv + 1 + o] = X[iv + o] + X[iv - 1 + o] - X[iv - 2 + o]
    # the phantom values are still zero here, as in the Fortran; these entries
    # of M are overwritten once they are filled in
    for f in range(-1, iv + 2):
        M[f + o] = (Y[f + 1 + o] - Y[f + o]) / (X[f + 1 + o] - X[f + o])
    cl = (M[2 + o] - M[1 + o]) / (X[3 + o] - X[1 + o])
    bl = M[1 + o] - cl * (X[2 + o] - X[1 + o])
    cr = (M[iv - 1 + o] - M[iv - 2 + o]) / (X[iv + o] - X[iv - 2 + o])
    br = M[iv - 1 + o] - cr * (X[iv - 1 + o] - X[iv + o])
    for f, edge, b_, c_ in (
        (0, 1, bl, cl),
        (-1, 1, bl, cl),
        (iv + 1, iv, br, cr),
        (iv + 2, iv, br, cr),
    ):
        d = X[f + o] - X[edge + o]
        Y[f + o] = Y[edge + o] + b_ * d + c_ * d * d
    M[-1 + o] = (Y[0 + o] - Y[-1 + o]) / (X[0 + o] - X[-1 + o])
    M[0 + o] = (Y[1 + o] - Y[0 + o]) / (X[1 + o] - X[0 + o])
    M[iv + o] = (Y[iv + 1 + o] - Y[iv + o]) / (X[iv + 1 + o] - X[iv + o])
    M[iv + 1 + o] = (Y[iv + 2 + o] - Y[iv + 1 + o]) / (X[iv + 2 + o] - X[iv + 1 + o])
    for f in range(-1, iv + 1):
        DM[f + o] = abs(M[f + 1 + o] - M[f + o])
    for i in range(1, iv + 1):
        den = DM[i + o] + DM[i - 2 + o]
        if den != 0.0:
            P[i + o] = DM[i + o] / den
            Q[i + o] = DM[i - 2 + o] / den
    for i in range(1, iv + 1):
        T[i + o] = P[i + o] * M[i - 1 + o] + Q[i + o] * M[i + o]
        if P[i + o] + Q[i + o] < np.finfo(float).tiny:
            T[i + o] = 0.5 * (M[i - 1 + o] + M[i + o])
    if not X[1 + o] <= x <= X[iv + o]:
        msg = f"s={x} lies outside the akima_spline knots"
        raise SystemExit(msg)
    i = max(1, min(iv - 1, int(np.searchsorted(xx, x, side="right"))))
    h = X[i + 1 + o] - X[i + o]
    c = (3 * M[i + o] - T[i + 1 + o] - 2 * T[i + o]) / h
    d = (T[i + 1 + o] + T[i + o] - 2 * M[i + o]) / (h * h)
    return float(X[i + o]), float(Y[i + o]), float(T[i + o]), float(c), float(d)


def akima_eval(xx, yy, x):
    """The Akima spline at x."""
    knot, a, b, c, d = akima_piece(xx, yy, x)
    t = x - knot
    return a + t * (b + t * (c + d * t))


def line_segment_piece(xx, yy, x):
    """The linear piece VMEC++ uses at x, as (knot, value, slope).

    This mirrors `evalLineSegment`, which picks the piece with a lower bound
    on the knots, so a point strictly inside a segment is carried by the
    segment above it; outside the knots the profile is flat.
    """
    n = len(xx)
    i = int(np.searchsorted(xx, x, side="left"))
    if i >= n - 1:
        return float(xx[n - 1]), float(yy[n - 1]), 0.0
    if i == 0:
        return float(xx[0]), float(yy[0]), 0.0
    x0, x1 = float(xx[i]), float(xx[i + 1])
    y0, y1 = float(yy[i]), float(yy[i + 1])
    return x0, y0, (y1 - y0) / (x1 - x0)


def integral_exponent(x, what):
    """x as a nonnegative integer, or a refusal."""
    if float(x) != int(x) or float(x) < 0:
        msg = f"{what} needs a nonnegative integral exponent, got {float(x)}"
        raise SystemExit(msg)
    return int(x)


def gauss_bumps(am):
    """How many Gaussian bumps of a two_power_gs profile to carry.

    VMEC skips a bump of zero amplitude; the expression language cannot
    branch, so the certificate carries every bump up to the last nonzero one
    and refuses if one of those has a zero width, which would divide by zero
    where VMEC would have skipped it.
    """
    g = 0
    for j in range(6):
        if 3 + 3 * j < len(am) and float(am[3 + 3 * j]) != 0.0:
            g = j + 1
    for j in range(g):
        if 5 + 3 * j >= len(am) or float(am[5 + 3 * j]) == 0.0:
            msg = (
                f"two_power_gs bump {j} has a zero width beneath a nonzero "
                "amplitude, which VMEC skips and a closed form cannot"
            )
            raise SystemExit(msg)
    return g


def _amj(am, j):
    """Slot j of the am array, which a wout may store short of 21 entries."""
    return float(am[j]) if j < len(am) else 0.0


def _poly(am, off, n, s):
    """A power series over the am slots offset by off."""
    return sum(_amj(am, off + j) * s**j for j in range(n))


def _dpoly(am, off, n, s):
    """Its derivative."""
    return sum(j * _amj(am, off + j) * s ** (j - 1) for j in range(1, n))


def pprime_ref(profile, am, s):
    """dp/ds of the certified profile, in floating point.

    This mirrors `pprime` of theories/Physics.v case by case, so that the
    bounds a point certificate claims are read against the profile it
    certifies rather than against a power series. The natural subtraction of
    the Rocq exponents saturates at zero, which is what max(.., 0) is doing
    here.
    """
    parts = profile.split()
    kind = parts[0]
    q = [int(x) for x in parts[1:]]
    if kind == "POWER":
        return _dpoly(am, 0, 21, s)
    if kind == "TWOPOWER":
        p, r = q
        return -_amj(am, 0) * p * r * s ** max(p - 1, 0) * (1.0 - s**p) ** max(r - 1, 0)
    if kind == "CUBIC":
        t = s - _amj(am, 4)
        return _amj(am, 1) + 2 * _amj(am, 2) * t + 3 * _amj(am, 3) * t * t
    if kind == "RATIONAL":
        nn, nd = q
        nu, de = _poly(am, 0, nn, s), _poly(am, 10, nd, s)
        return (_dpoly(am, 0, nn, s) * de - nu * _dpoly(am, 10, nd, s)) / de**2
    if kind == "GAUSSTRUNC":
        inv1 = 1.0 / _amj(am, 1)
        num = _amj(am, 0) * np.exp(-((s * inv1) ** 2)) * (-2.0 * s * inv1**2)
        return num / (1.0 - np.exp(-(inv1**2)))
    if kind == "TWOPOWERGS":
        p, r, g = q
        tp = _amj(am, 0) * (1.0 - s**p) ** r
        tpd = -_amj(am, 0) * p * r * s ** max(p - 1, 0) * (1.0 - s**p) ** max(r - 1, 0)
        gv, gd = 1.0, 0.0
        for j in range(g):
            amp, ctr, wid = (_amj(am, 3 + 3 * j), _amj(am, 4 + 3 * j), _amj(am, 5 + 3 * j))
            x = (s - ctr) / wid
            e = np.exp(-x * x)
            gv += amp * e
            gd += amp * e * (-2.0 * x / wid)
        return tpd * gv + tp * gd
    if kind == "PEDESTAL":
        ctr, wid = _amj(am, 18), _amj(am, 19)
        t1 = np.tanh(2.0 * (ctr - np.sqrt(s)) / wid)
        te = np.tanh(2.0 * (ctr - 1.0) / wid)
        t0 = np.tanh(2.0 * ctr / wid)
        nn = 1.0 / (t0 - te)
        tail = nn * _amj(am, 17) * (1.0 - t1 * t1) * (-1.0 / (wid * np.sqrt(s)))
        return _dpoly(am, 0, 16, s) + tail
    if kind == "TWOLORENTZ":
        p, r, rr, tt = q

        def dfac(a, pp, qq):
            z = s / (a * a)
            return -(pp * qq) * (z ** max(pp - 1, 0) / (a * a)) / (1.0 + z**pp) ** (qq + 1)

        def efac(a, pp, qq):
            z = 1.0 / (a * a)
            return 1.0 / (1.0 + z**pp) ** qq

        a1 = _amj(am, 1)
        return _amj(am, 0) * (
            a1 * dfac(_amj(am, 2), p, r) / (1.0 - efac(_amj(am, 2), p, r))
            + (1.0 - a1)
            * dfac(_amj(am, 5), rr, tt)
            / (1.0 - efac(_amj(am, 5), rr, tt))
        )
    msg = f"no float reference for profile {profile!r}"
    raise SystemExit(msg)


def output_line(a):
    """The OUTPUT line: what the three components of the certificate carry."""
    if a.terms:
        return "radial-terms" if a.radial else "terms"
    if a.stream_defect:
        return "stream-defect"
    if a.boozer:
        return "boozer " + a.boozer.replace(",", " ")
    if a.covariant:
        return "covariant " + a.covariant.replace(",", " ")
    if a.covariant_sin:
        return "covariant-sin " + a.covariant_sin.replace(",", " ")
    if a.radial and (a.axis or a.edge):
        return "radial-axis"
    if a.radial and a.shear:
        return "radial-shear"
    if a.radial and a.geometry:
        # the free-radius reconstruction, read for the Jacobian and its radial
        # derivative, whose angular integrals are dV/ds and V''
        return "radial-geometry"
    if a.mercier:
        return "mercier-" + a.mercier
    if a.geometry:
        return "geometry"
    if a.harmonic:
        return "harmonic " + a.harmonic.replace(",", " ")
    if a.radial:
        return "radial"
    return "residual"


def classify_pressure(ptype, am):
    """The PROFILE line for a VMEC pmass_type, or a refusal.

    Piecewise profiles are not resolved here: the piece containing the node's
    s depends on the node, so it is emitted per node as a local cubic, the
    linear ones with their quadratic and cubic coefficients zero.
    """
    if ptype in ("power_series", ""):
        return "POWER"
    if ptype == "two_power":
        p = integral_exponent(am[1], "two_power")
        q = integral_exponent(am[2], "two_power")
        return f"TWOPOWER {p} {q}"
    if ptype == "two_power_gs":
        p = integral_exponent(am[1], "two_power_gs")
        q = integral_exponent(am[2], "two_power_gs")
        return f"TWOPOWERGS {p} {q} {gauss_bumps(am)}"
    if ptype == "gauss_trunc":
        return "GAUSSTRUNC"
    if ptype == "rational":
        return "RATIONAL 10 11"
    if ptype == "two_lorentz":
        if float(am[2]) == 0.0 or float(am[5]) == 0.0:
            msg = "two_lorentz with a zero width divides by zero"
            raise SystemExit(msg)
        p = integral_exponent(am[3], "two_lorentz")
        q = integral_exponent(am[4], "two_lorentz")
        r = integral_exponent(am[6], "two_lorentz")
        t = integral_exponent(am[7], "two_lorentz")
        return f"TWOLORENTZ {p} {q} {r} {t}"
    if ptype == "pedestal":
        # a nonpositive width switches the tanh term off, leaving the
        # sixteen-term polynomial, which is a power series
        if float(am[19]) <= 0.0:
            return "PEDESTAL_OFF"
        return "PEDESTAL"
    if ptype == "cubic_spline":
        # resolved per node, since the piece depends on where the node sits
        return "SPLINE"
    if ptype == "akima_spline":
        return "AKIMA"
    if ptype == "line_segment":
        return "SEGMENT"
    msg = f"pressure parameterization {ptype!r} is not certified"
    raise SystemExit(msg)


class Wout:
    """The wout fields the certificate needs.

    Reads either a VMEC netCDF wout, whose Fourier arrays are (ns, mnmax),
    or a VMEC++ output HDF5, whose wout group holds them transposed.
    """

    def __init__(self, path):
        """Load the fields and classify the pressure parameterization."""
        if str(path).endswith(".h5"):
            self._from_h5(path)
        else:
            self._from_nc(path)
        self.h = 1.0 / (self.ns - 1)
        self.s_full = np.arange(self.ns) * self.h
        self.s_half = (np.arange(self.ns) - 0.5) * self.h  # row j of lmns

    def _from_nc(self, path):
        """Read a VMEC netCDF wout."""
        import netCDF4

        d = netCDF4.Dataset(path)
        d.set_auto_mask(False)
        v = d.variables

        def g(k):
            return np.asarray(v[k][:], dtype=float)

        self.ns = int(v["ns"][:])
        self.xm = g("xm").astype(int)
        self.xn = g("xn").astype(int)
        self.rmnc = g("rmnc")
        self.zmns = g("zmns")
        self.lmns = g("lmns")
        self.iotas = g("iotas")
        self.phips = g("phips")
        self.am = g("am")
        self.lasym = bool(int(v["lasym__logical__"][:])) if "lasym__logical__" in v else False
        if self.lasym:
            self.rmns = g("rmns")
            self.zmnc = g("zmnc")
            self.lmnc = g("lmnc")
        ptype = v["pmass_type"][:].tobytes().decode().replace(chr(0), "").strip()
        self.profile = classify_pressure(ptype, self.am)
        if self.profile in ("SPLINE", "AKIMA", "SEGMENT"):
            self.aux_s = g("am_aux_s")
            self.aux_f = g("am_aux_f")
            self.pres_half = g("pres")
        d.close()

    def _from_h5(self, path):
        """Read the wout group of a VMEC++ output file."""
        import h5py

        f = h5py.File(path, "r")
        w = f["wout"] if "wout" in f else f

        def g(k):
            return np.asarray(w[k][()], dtype=float)

        def gt(k):
            # (mnmax, ns) in the VMEC++ layout, (ns, mnmax) here
            return np.asarray(w[k][()], dtype=float).T

        self.ns = int(w["ns"][()])
        self.xm = np.asarray(w["xm"][()]).astype(int)
        self.xn = np.asarray(w["xn"][()]).astype(int)
        self.rmnc = gt("rmnc")
        self.zmns = gt("zmns")
        self.lmns = gt("lmns")
        self.iotas = g("iotas")
        self.phips = g("phips")
        self.am = g("am")
        self.lasym = bool(int(np.asarray(w["lasym"][()])))
        if self.lasym:
            self.rmns = gt("rmns")
            self.zmnc = gt("zmnc")
            self.lmnc = gt("lmnc")
        ptype = w["pmass_type"][()]
        ptype = ptype.decode() if isinstance(ptype, bytes) else str(ptype)
        self.profile = classify_pressure(ptype.replace(chr(0), "").strip(), self.am)
        if self.profile in ("SPLINE", "AKIMA", "SEGMENT"):
            self.aux_s = g("am_aux_s")
            self.aux_f = g("am_aux_f")
            self.pres_half = g("pres")
        f.close()


# ----- float reference of the same rule, for choosing eps -----------------


def half_coefs(w, j_in, j_out, s_h, coefs):
    """c(h) and c'(h) of every mode between full nodes j_in and j_out, by
    VMEC's parity-aware rule."""
    ya, yb = coefs[j_in], coefs[j_out]
    s_a, s_b = w.s_full[j_in], w.s_full[j_out]
    odd = (w.xm % 2) == 1
    c = 0.5 * (ya + yb)
    cs = (yb - ya) / (s_b - s_a)
    qa, qb = ya / np.sqrt(s_a), yb / np.sqrt(s_b)
    c_odd = np.sqrt(s_h) * 0.5 * (qa + qb)
    cs_odd = np.sqrt(s_h) * (qb - qa) / (s_b - s_a) + c_odd / (2.0 * s_h)
    return np.where(odd, c_odd, c), np.where(odd, cs_odd, cs)


def half_point(w, j_in, j_out, row_l, u, vv, phip):
    """B^u, B^v, B_u, B_v, d_u B_s, d_v B_s and mu0 sqrtg J^s at the half point.

    Carries both parities: R is a cosine series plus, when lasym, a sine
    series; Z and lambda are sine series plus cosine series. This is the
    reconstruction of theories/Physics.v, evaluated in floating point to
    choose the claimed bounds.
    """
    m, n = w.xm, w.xn
    s_h = w.s_half[row_l]
    cR, cRs = half_coefs(w, j_in, j_out, s_h, w.rmnc)
    cZ, cZs = half_coefs(w, j_in, j_out, s_h, w.zmns)
    cL = w.lmns[row_l]
    iota = float(w.iotas[row_l])
    ang = m * u - n * vv
    c = np.cos(ang)
    sn = np.sin(ang)

    def S(cf, k):
        return float(np.dot(cf, k))

    def ser(cf, even):
        """Value and the five angular derivatives of one parity's series."""
        if even:
            k0, k1, su, sv = c, sn, -m, n
        else:
            k0, k1, su, sv = sn, c, m, -n
        return np.array([
            S(cf, k0), S(cf, su * k1), S(cf, sv * k1),
            S(cf, -m * m * k0), S(cf, m * n * k0), S(cf, -n * n * k0),
        ])

    if w.lasym:
        cRa, cRas = half_coefs(w, j_in, j_out, s_h, w.rmns)
        cZa, cZas = half_coefs(w, j_in, j_out, s_h, w.zmnc)
        cLa = w.lmnc[row_l]
        R_, R_s_ = ser(cR, True) + ser(cRa, False), ser(cRs, True) + ser(cRas, False)
        Z_, Z_s_ = ser(cZ, False) + ser(cZa, True), ser(cZs, False) + ser(cZas, True)
        L_ = ser(cL, False) + ser(cLa, True)
    else:
        R_, R_s_ = ser(cR, True), ser(cRs, True)
        Z_, Z_s_ = ser(cZ, False), ser(cZs, False)
        L_ = ser(cL, False)

    R, R_u, R_v, R_uu, R_uv, R_vv = R_
    R_s, R_su, R_sv = R_s_[0], R_s_[1], R_s_[2]
    _Z, Z_u, Z_v, Z_uu, Z_uv, Z_vv = Z_
    Z_s, Z_su, Z_sv = Z_s_[0], Z_s_[1], Z_s_[2]
    _L, L_u, L_v, L_uu, L_uv, L_vv = L_

    tau = R_u * Z_s - R_s * Z_u
    sqrtg = R * tau
    tau_u = R_uu * Z_s + R_u * Z_su - R_su * Z_u - R_s * Z_uu
    tau_v = R_uv * Z_s + R_u * Z_sv - R_sv * Z_u - R_s * Z_uv
    g_u = R_u * tau + R * tau_u
    g_v = R_v * tau + R * tau_v
    guu = R_u**2 + Z_u**2
    guv = R_u * R_v + Z_u * Z_v
    gvv = R_v**2 + Z_v**2 + R**2
    gsu = R_s * R_u + Z_s * Z_u
    gsv = R_s * R_v + Z_s * Z_v
    gsu_u = R_su * R_u + R_s * R_uu + Z_su * Z_u + Z_s * Z_uu
    gsu_v = R_sv * R_u + R_s * R_uv + Z_sv * Z_u + Z_s * Z_uv
    gsv_u = R_su * R_v + R_s * R_uv + Z_su * Z_v + Z_s * Z_uv
    gsv_v = R_sv * R_v + R_s * R_vv + Z_sv * Z_v + Z_s * Z_vv
    guu_v = 2 * (R_u * R_uv + Z_u * Z_uv)
    guv_u = R_uu * R_v + R_u * R_uv + Z_uu * Z_v + Z_u * Z_uv
    guv_v = R_uv * R_v + R_u * R_vv + Z_uv * Z_v + Z_u * Z_vv
    gvv_u = 2 * (R_v * R_uv + Z_v * Z_uv + R * R_u)
    bu = iota - L_v
    bv = 1.0 + L_u
    Bu = phip * bu / sqrtg
    Bv = phip * bv / sqrtg
    Bu_u = phip * (-L_uv * sqrtg - bu * g_u) / sqrtg**2
    Bv_u = phip * (L_uu * sqrtg - bv * g_u) / sqrtg**2
    Bu_v = phip * (-L_vv * sqrtg - bu * g_v) / sqrtg**2
    Bv_v = phip * (L_uv * sqrtg - bv * g_v) / sqrtg**2
    B_u = guu * Bu + guv * Bv
    B_v = guv * Bu + gvv * Bv
    B_s_u = gsu_u * Bu + gsu * Bu_u + gsv_u * Bv + gsv * Bv_u
    B_s_v = gsu_v * Bu + gsu * Bu_v + gsv_v * Bv + gsv * Bv_v
    B_u_v = guu_v * Bu + guu * Bu_v + guv_v * Bv + guv * Bv_v
    B_v_u = guv_u * Bu + guv * Bu_u + gvv_u * Bv + gvv * Bv_u
    mu0Js = B_v_u - B_u_v
    B2 = Bu * B_u + Bv * B_v
    return {
        "Bu": Bu,
        "Bv": Bv,
        "B_u": B_u,
        "B_v": B_v,
        "B_s_u": B_s_u,
        "B_s_v": B_s_v,
        "mu0Js": mu0Js,
        "B2": B2,
    }


def residual_ref(w, j, u, vv, phip):
    """Float reference of the residual at node j, for choosing bounds."""
    qm = half_point(w, j - 1, j, j, u, vv, phip)  # h- = row j of the half grid
    qp = half_point(w, j, j + 1, j + 1, u, vv, phip)  # h+ = row j+1
    h = w.s_half[j + 1] - w.s_half[j]
    avg = lambda k: 0.5 * (qm[k] + qp[k])  # noqa: E731
    dif = lambda k: (qp[k] - qm[k]) / h  # noqa: E731
    s = w.s_full[j]
    pp = pprime_ref(w.profile, w.am, s)
    rs = (avg("B_s_v") - dif("B_v")) * avg("Bv") - (dif("B_u") - avg("B_s_u")) * avg("Bu") - MU0 * pp
    ru = -qp["mu0Js"] * qp["Bv"]
    rv_ = qp["mu0Js"] * qp["Bu"]
    return rs, ru, rv_, max(qm["B2"], qp["B2"])


ANGLE_EXP = -50
RAD_EXP = -50


def dyadic_at(x, e=ANGLE_EXP):
    """x on the fixed dyadic grid of step 2^e, as (mantissa, e).

    The angles have to share a fine exponent: the checker varies the mantissa
    of the angle slot, so one mantissa unit is 2^e radians, and taking whatever
    exponent the double happens to carry makes the unit meaningless (u = 0 has
    exponent 0, one unit of which is a radian).
    """
    return round(float(x) / 2.0**e), e


def slot3_width(a):
    """Half-width of the third slot, in mantissa units of its own exponent.

    The default is pi, so that one cell spans the whole toroidal angle. For an
    axisymmetric equilibrium that costs nothing, since toroidal_terms_vanish
    makes the derivative along it the zero expression, and it turns a covering
    of a cross-section into a covering of the volume inside the verdict.
    """
    w = np.pi if a.dw3 is None else a.dw3
    return int(np.ceil(w / 2.0**ANGLE_EXP))


def tile(width, n, e, scale=1.0):
    """Centres and half-width of n abutting cells of total span >= width.

    `scale` shrinks the half-width without moving the centres, which leaves
    gaps between the cells. That is for diagnosis: a covering like it is not a
    tiling, the quadrature theorems do not apply to it, and the checker
    refuses to integrate it.

    Everything is in units of 2**e, so the cells are exactly the tiling
    theories/Cover.v reasons about: cell k is centred at (2k+1)d with
    half-width d, consecutive cells share an endpoint, and the run covers
    [0, 2nd]. Rounding a centre onto the grid after choosing it in radians
    would leave the cells a fraction of an ulp apart, which is enough to put
    them outside the theorem even though it is far too small to matter
    numerically.
    """
    d = int(np.ceil(width / (2.0 * n) / 2.0**e))
    return [(2 * k + 1) * d for k in range(n)], max(1, int(round(d * scale)))


def stream_coeffs(w, j, phip, nu=256, nv=64):
    """The Boozer stream function of the outer half point of node j.

    w is defined by B_u = I + d_u w and B_v = G + d_v w, so its coefficients
    follow from those of the covariant components, which are projections onto
    the angular kernels. This is a float pass: nothing here is certified, and
    what makes the result usable is that `--stream-defect` bounds how far the
    numbers it produces are from satisfying those two relations.
    """
    m, n = w.xm, w.xn
    axisym = not (n != 0).any()
    if axisym:
        nv = 1
    us = 2.0 * np.pi * np.arange(nu) / nu
    vs = 2.0 * np.pi * np.arange(nv) / nv
    K = len(m)
    acc_u = np.zeros(K)
    acc_v = np.zeros(K)
    tot_u = 0.0
    tot_v = 0.0
    for u in us:
        for vv in vs:
            q = half_point(w, j, j + 1, j + 1, u, vv, phip)
            ang = m * u - n * vv
            c = np.cos(ang)
            acc_u += q["B_u"] * c
            acc_v += q["B_v"] * c
            tot_u += q["B_u"]
            tot_v += q["B_v"]
    npts = nu * nv
    # the mean is the (0, 0) coefficient; the others carry the factor of two
    # a cosine projection over the whole torus leaves
    I = tot_u / npts
    G = tot_v / npts
    a = 2.0 * acc_u / npts
    c = 2.0 * acc_v / npts
    wc = np.zeros(K)
    for k in range(K):
        if m[k] != 0:
            wc[k] = a[k] / m[k]
        elif n[k] != 0:
            wc[k] = -c[k] / n[k]
        else:
            wc[k] = 0.0
    return wc, float(I), float(G)


def coef_slot(w, K, block, row, mode):
    """The environment slot of one coefficient, in the layout Physics.v fixes."""
    off = {"rmnc": 0, "zmns": 3 * K, "lmns": 6 * K}[block]
    if block == "lmns" and row > 1:
        msg = "lambda has two rows, h- and h+"
        raise SystemExit(msg)
    return 32 + off + row * K + mode


def write_coefbox(a, w, K, phip, j, us, v0):
    """A certificate whose cells range over a coefficient and an angle.

    Cell.v varies any two input slots, and nothing in it is about angles, so
    putting a coefficient among them costs no new theorem. What changes is
    what a floor verdict says: instead of excluding the one field the file
    names, it excludes every field whose coefficient lies in the box, at every
    angle the cells cover. That is the difference between "this reconstruction
    is out of balance here" and "no reconstruction of this family is".
    """
    block, row, mode, half = a.coefbox.split(",")
    row, mode, half = int(row), int(mode), float(half)
    slot = coef_slot(w, K, block, row, mode)
    arr = {"rmnc": w.rmnc, "zmns": w.zmns, "lmns": w.lmns}[block]
    # the row of the node stencil this is, and the coefficient itself
    src = (j - 1 + row) if block != "lmns" else (j + row)
    m_coef, e_coef = dyadic(arr[src][mode])
    d_coef = max(1, int(round(half * abs(m_coef))))
    lines = []
    P = lines.append
    P("STELLAROCQ-CCERT 7")
    P(f"PREC {a.prec}")
    P(f"LASYM {1 if w.lasym else 0}")
    P(f"PROFILE {w.profile}")
    P(f"SLOTS {slot} 1")
    P("OUTPUT " + output_line(a))
    P(f"MODES {K}")
    for m, n in zip(w.xm, w.xn, strict=True):
        P(f"{m} {n}")
    P("PHIP {} {}".format(*dyadic(phip)))
    P("AM 21")
    for i in range(21):
        am_i = w.am[i] if i < len(w.am) else 0.0
        P("{} {}".format(*dyadic(am_i)))

    ums, du = tile(2.0 * np.pi, len(us), ANGLE_EXP)
    mv0 = dyadic_at(v0)[0]
    P(f"NANGLES {len(ums)}")
    for mu in ums:
        # the first half-width belongs to the varied coefficient, the second
        # to the poloidal angle
        P(f"{mu} {ANGLE_EXP} {mv0} {ANGLE_EXP} {d_coef} {du}")

    P("NNODES 1")
    P("NODE")
    P("S {} {}".format(*dyadic(w.s_full[j])))
    P("SNODES " + " ".join("{} {}".format(*dyadic(x))
                           for x in w.s_full[j - 1 : j + 2]))
    P("SHALF " + " ".join("{} {}".format(*dyadic(x))
                          for x in w.s_half[j : j + 2]))
    P("IOTA " + " ".join("{} {}".format(*dyadic(x))
                         for x in w.iotas[j : j + 2]))
    blocks = [
        ("RNODES", w.rmnc[j - 1 : j + 2]),
        ("ZNODES", w.zmns[j - 1 : j + 2]),
        ("LHALF", w.lmns[j : j + 2]),
    ]
    if w.lasym:
        blocks += [
            ("RNODES_A", w.rmns[j - 1 : j + 2]),
            ("ZNODES_A", w.zmnc[j - 1 : j + 2]),
            ("LHALF_A", w.lmnc[j : j + 2]),
        ]
    for tag, M in blocks:
        P(tag)
        for r in M:
            P(" ".join("{} {}".format(*dyadic(x)) for x in r))
    P(f"CELLS {len(ums)}")
    for _ in ums:
        for _ in range(3):
            P("1 0 1 0 1 0 4 0")
    pathlib.Path(a.out).write_text("\n".join(lines) + "\n")
    rel = d_coef / abs(m_coef) if m_coef else 0.0
    print(f"wrote {a.out}: {len(ums)} cells over {block}[{src},{mode}] "
          f"and the poloidal angle, K={K}")
    print(f"the coefficient box is {arr[src][mode]:.9e} "
          f"+- {rel:.3%}, at slot {slot}")
    print("run 'main --tighten --lower --filter' on it, then 'main --lower'")


def write_ccert(a, w, K, phip, idx, us, vs, nv, three_d):
    """Write a cell certificate: every angle of every cell is covered.

    A cell spans half a spacing either side of its centre angle, so the cells
    of an axisymmetric case tile the whole angular torus and those of a
    three-dimensional case tile u in [0, 2 pi) at each of nv toroidal angles.
    The half-widths are carried in units of the mantissa of the centre angle,
    which is what the checker varies, and the bounds are left to
    "main --tighten".
    """
    wu = a.wscale * np.pi / len(us)
    # An axisymmetric equilibrium has every n zero, so the v derivative of the
    # residual is the zero expression (theories/Identities.v,
    # toroidal_terms_vanish) and one cell covers the whole toroidal angle at
    # no cost. A three-dimensional one has to resolve the v extent as finely
    # as the u extent, which squares the cell count, so by default its cells
    # are u segments at nv toroidal angles; --surface gives them toroidal
    # width instead and the covering becomes a patch of the surface.
    if not three_d:
        wv = a.wscale * np.pi
    elif a.surface:
        wv = a.wscale * np.pi / len(vs)
    else:
        wv = 0.0
    lines = []
    P = lines.append
    P("STELLAROCQ-CCERT 7")
    P(f"PREC {a.prec}")
    P(f"LASYM {1 if w.lasym else 0}")
    P(f"PROFILE {w.profile}")
    P(f"SLOTS {a.slots}")
    if a.slot3 is not None:
        P(f"SLOT3 {a.slot3} {slot3_width(a)}")
    P("OUTPUT " + output_line(a))
    P(f"MODES {K}")
    for m, n in zip(w.xm, w.xn, strict=True):
        P(f"{m} {n}")
    P("PHIP {} {}".format(*dyadic(phip)))
    P("AM 21")
    for j in range(21):
        am_j = w.am[j] if j < len(w.am) else 0.0
        P("{} {}".format(*dyadic(am_j)))

    # The poloidal cells are an exact tiling of [0, 2 pi) in mantissa units.
    ums, du = tile(2.0 * np.pi, len(us), ANGLE_EXP, a.wscale)
    if wv > 0:
        vms, dv = tile(2.0 * np.pi, len(vs), ANGLE_EXP, a.wscale)
    else:
        vms, dv = [dyadic_at(v)[0] for v in vs], 0
    angles = [(mu, mv) for mu in ums for mv in vms]
    P(f"NANGLES {len(angles)}")
    for mu, mv in angles:
        P(f"{mu} {ANGLE_EXP} {mv} {ANGLE_EXP} {du} {dv}")

    P(f"NNODES {len(idx)}")
    for j in idx:
        P("NODE")
        P("S {} {}".format(*dyadic(w.s_full[j])))
        P("SNODES " + " ".join("{} {}".format(*dyadic(x)) for x in w.s_full[j - 1 : j + 2]))
        P("SHALF " + " ".join("{} {}".format(*dyadic(x)) for x in w.s_half[j : j + 2]))
        P("IOTA " + " ".join("{} {}".format(*dyadic(x)) for x in w.iotas[j : j + 2]))
        blocks = [
            ("RNODES", w.rmnc[j - 1 : j + 2]),
            ("ZNODES", w.zmns[j - 1 : j + 2]),
            ("LHALF", w.lmns[j : j + 2]),
        ]
        if w.lasym:
            blocks += [
                ("RNODES_A", w.rmns[j - 1 : j + 2]),
                ("ZNODES_A", w.zmnc[j - 1 : j + 2]),
                ("LHALF_A", w.lmnc[j : j + 2]),
            ]
        for tag, M in blocks:
            P(tag)
            for row in M:
                P(" ".join("{} {}".format(*dyadic(x)) for x in row))
        if a.stream_defect or a.boozer:
            wc, I_, G_ = stream_coeffs(w, j, phip)
            P(f"WCOEF {K}")
            for x in wc:
                P("{} {}".format(*dyadic(x)))
            P("{} {}".format(*dyadic(I_)))
            P("{} {}".format(*dyadic(G_)))
        P(f"CELLS {len(angles)}")
        # The bounds are placeholders that "main --tighten" replaces with the
        # enclosures the checker computes, because the width of an interval
        # enclosure of a cancelling expression is a property of the arithmetic
        # and cannot be predicted from a float sample of the function.
        blank = "1 0 1 0 1 0 4 0" + (" 1 0" if a.slot3 is not None else "")
        for _ in angles:
            for _ in range(3):
                P(blank)
    pathlib.Path(a.out).write_text("\n".join(lines) + "\n")
    print(
        f"wrote {a.out}: {len(idx)} nodes x {len(angles)} cells = "
        f"{len(idx) * len(angles)} cells, K={K}"
    )
    if not three_d or a.surface:
        cover = (
            f"the cells tile the whole angular torus, {len(us)} by {len(vs)}"
        )
    else:
        cover = f"the cells tile u in [0, 2 pi) at each of {nv} toroidal angles"
    print(f"cell half-widths: u {wu:.4e} rad, v {wv:.4e} rad; {cover}")
    if a.harmonic:
        # a float reference for the integral the checker will enclose, so a
        # run can be read against something
        hm, hn = (float(x) for x in a.harmonic.split(","))
        N = 4096
        uu = np.linspace(0, 2 * np.pi, N, endpoint=False)
        step = 2 * np.pi / N
        for j in idx:
            acc = np.zeros(3)
            for x in uu:
                r = residual_ref(w, j, x, vs[0], phip)[:3]
                acc += np.array(r) * np.cos(hm * x - hn * vs[0])
            acc *= step
            print(
                f"  node {j:3d} reference harmonic: r_s {acc[0]:.4e} "
                f"r_u {acc[1]:.4e} r_v {acc[2]:.4e}"
            )
    print("run 'main --tighten' on it to set the bounds, then check the result")


def read_profile(path):
    """The measured resolution per node, from gen/nrad_profile.py."""
    prof = {}
    for line in pathlib.Path(path).read_text().splitlines():
        m = re.match(r"\s*node\s+(\d+):\s*(\d+)x", line)
        if m:
            prof[int(m.group(1))] = int(m.group(2))
    if not prof:
        msg = f"{path} carries no 'node N: Mx' lines"
        raise SystemExit(msg)
    return prof


def nrad_at(a, w, j):
    """Radial cells for node j.

    Uniform unless --adapt, which spends cells where the worst case is set,
    or --adapt-from, which reads that from a measurement instead.

    That is against the axis. The parity rule divides by sqrt(s) and the field
    quantities carry 1/(2s) and 1/(4s^2), so a radial box of a given width
    encloses far more loosely there than further out, and the worst cell of a
    whole plasma is always an inner one. Coarsening the inner region to pay
    for the outer one costs orders of magnitude: measured on solovev, a
    profile four times coarser inside took the worst bound from 5.6e-01 to
    3.6e+02. The outer region contributes nothing to the worst case and is
    where cells can be saved.
    """
    if a.adapt_from is not None:
        if not hasattr(a, "_profile"):
            a._profile = read_profile(a.adapt_from)
        return a.nrad * a._profile.get(j, 1)
    if not a.adapt:
        return a.nrad
    s = float(w.s_full[j])
    if s < 0.1:
        return 4 * a.nrad
    if s < 0.25:
        return 2 * a.nrad
    return a.nrad


def write_rcert(a, w, K, phip, idx, us, v0):
    """Write a radial cell certificate: a cell covers a rectangle of radius
    and poloidal angle, so a VALID verdict holds between surfaces and not
    only on one.

    Slot 0 is the radius the whole reconstruction reads, so a cell of
    Cell.v ranging over slots 0 and 1 is a radial-by-poloidal rectangle.
    The radius of a cell is carried by the NODE block it belongs to and the
    poloidal angle by the cell list every node shares, so one node block is
    emitted per radial cell, differing only in its S line.

    A node's piece runs from its inner half point to its outer one, which
    is the interval the Hermite of theories/Physics.v is built on, so
    consecutive nodes tile the radius with no gap and no overlap.
    """
    hs = w.h
    wu = a.wscale * np.pi / len(us)
    lines = []
    P = lines.append
    P("STELLAROCQ-CCERT 7")
    P(f"PREC {a.prec}")
    P(f"LASYM {1 if w.lasym else 0}")
    P(f"PROFILE {w.profile}")
    P("SLOTS 0 1")
    if a.slot3 is not None:
        P(f"SLOT3 {a.slot3} {slot3_width(a)}")
    P("OUTPUT " + output_line(a))
    P(f"MODES {K}")
    for m, n in zip(w.xm, w.xn, strict=True):
        P(f"{m} {n}")
    P("PHIP {} {}".format(*dyadic(phip)))
    P("AM 21")
    for j in range(21):
        am_j = w.am[j] if j < len(w.am) else 0.0
        P("{} {}".format(*dyadic(am_j)))

    # the poloidal cells, an exact tiling shared by every radial cell
    P(f"NANGLES {len(us)}")
    ums, dv = tile(2.0 * np.pi, len(us), ANGLE_EXP, a.wscale)
    dr_half = hs / (2.0 * a.nrad)
    # one extra unit of radial half-width, so that the runs of consecutive
    # nodes overlap rather than gap where their endpoints round apart
    du = int(np.ceil(dr_half / 2.0**RAD_EXP)) + 1
    mv0 = dyadic_at(v0)[0]
    for mu in ums:
        P(f"{mu} {ANGLE_EXP} {mv0} {ANGLE_EXP} {du} {dv}")

    # one node block per radial cell
    # Each node's radial cells are an exact tiling of its half-grid interval,
    # laid out in mantissa units so the centres abut without rounding. With
    # --adapt a node carries its own resolution: the bound near the axis is the
    # continuum residual and stops falling however fine the cells get, while
    # further out it is still the enclosure and refinement keeps paying, so
    # spending cells uniformly spends them where they do nothing.
    # A node's cells tile its half-grid interval. Where a piecewise pressure
    # has a knot inside that interval the tiling is split there, so no cell
    # ever spans two pieces and every cell has a cubic that is exact on it.
    piecewise = hasattr(w, "piece_am")
    radii = []
    for j in idx:
        # a node's cells tile the interval between its two half points, except
        # at the two ends, where the two-node rule tiles between the nodes
        # themselves and so reaches the axis side and the boundary
        if a.edge:
            lo_s, hi_s = float(w.s_full[j]), float(w.s_full[j + 1])
        else:
            lo_s, hi_s = float(w.s_half[j]), float(w.s_half[j + 1])
        cuts = [lo_s, hi_s]
        if piecewise:
            cuts = sorted({lo_s, hi_s}
                          | {k for k in w.knots if lo_s < k < hi_s})
        nr = nrad_at(a, w, j)
        for seg in range(len(cuts) - 1):
            a_s, b_s = cuts[seg], cuts[seg + 1]
            m_lo = round(a_s / 2.0**RAD_EXP)
            m_hi = round(b_s / 2.0**RAD_EXP)
            # cells of this segment, in mantissa units, sharing an endpoint
            n_seg = max(1, int(round(nr * (b_s - a_s) / (hi_s - lo_s))))
            dj = max(1, (m_hi - m_lo + 2 * n_seg - 1) // (2 * n_seg)) + 1
            am_seg = w.piece_am(0.5 * (a_s + b_s)) if piecewise else None
            for i in range(n_seg):
                radii.append((j, m_lo + (2 * i + 1) * dj, dj, am_seg))
    P(f"NNODES {len(radii)}")
    prev_j = None
    for j, mc, dj, am_seg in radii:
        # Consecutive cells of one node differ only in where they sit, so the
        # coefficient blocks are written once and the rest say SAME. At the
        # cell counts a volume covering needs this is the difference between
        # a file of tens of megabytes and one of a few.
        P("NODE SAME" if j == prev_j else "NODE")
        P(f"S {mc} {RAD_EXP}")
        P(f"DU {dj}")
        if am_seg is not None:
            P("AMLOCAL 21")
            for x in am_seg:
                P("{} {}".format(*dyadic(x)))
        if j != prev_j:
            P("SNODES " + " ".join("{} {}".format(*dyadic(x))
                                   for x in w.s_full[j - 1 : j + 2]))
            P("SHALF " + " ".join("{} {}".format(*dyadic(x))
                                  for x in w.s_half[j : j + 2]))
            P("IOTA " + " ".join("{} {}".format(*dyadic(x))
                                 for x in w.iotas[j : j + 2]))
            blocks = [
                ("RNODES", w.rmnc[j - 1 : j + 2]),
                ("ZNODES", w.zmns[j - 1 : j + 2]),
                ("LHALF", w.lmns[j : j + 2]),
            ]
            if w.lasym:
                blocks += [
                    ("RNODES_A", w.rmns[j - 1 : j + 2]),
                    ("ZNODES_A", w.zmnc[j - 1 : j + 2]),
                    ("LHALF_A", w.lmnc[j : j + 2]),
                ]
            for tag, M in blocks:
                P(tag)
                for row in M:
                    P(" ".join("{} {}".format(*dyadic(x)) for x in row))
        prev_j = j
        P(f"CELLS {len(us)}")
        blank = "1 0 1 0 1 0 4 0" + (" 1 0" if a.slot3 is not None else "")
        for _ in us:
            for _ in range(3):
                P(blank)
    pathlib.Path(a.out).write_text("\n".join(lines) + "\n")
    print(
        f"wrote {a.out}: {len(radii)} radial x {len(us)} poloidal = "
        f"{len(radii) * len(us)} cells, K={K}"
    )
    print(
        f"cell half-widths: s {du * 2.0**RAD_EXP:.4e}, u {wu:.4e} rad; the cells tile "
        f"each node's half-grid interval and the whole poloidal angle"
    )
    print("run 'main --tighten' on it to set the bounds, then check the result")


def main():
    """Read the wout, choose the bounds, write the certificate."""
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("out")
    ap.add_argument(
        "--cells",
        action="store_true",
        help="emit a cell certificate: the bound holds at every angle of each "
        "cell, not only at its centre",
    )
    ap.add_argument(
        "--surface",
        action="store_true",
        help="give the toroidal angle real cell width, so that the cells of a "
        "three-dimensional case tile a patch of the surface rather than a "
        "curve on it. --nv is then the number of toroidal cells over the "
        "whole 2 pi.",
    )
    ap.add_argument(
        "--wscale",
        type=float,
        default=1.0,
        help="scale the cell half-widths. 1 makes the cells tile the angular "
        "torus exactly; smaller leaves gaps and is for diagnosis only.",
    )
    ap.add_argument(
        "--radial",
        action="store_true",
        help="cover a rectangle of radius and poloidal angle instead of a "
        "patch of one surface: the cells range over slot 0, the radius the "
        "reconstruction reads, so the verdict holds between surfaces rather "
        "than on one. A node's cells tile the interval between its two half "
        "points.",
    )
    ap.add_argument(
        "--axis",
        action="store_true",
        help="cover the innermost interval, between the first two half "
        "points, where the coefficients are read from the two innermost "
        "nodes by the parity-scaled linear rule because no inner half point "
        "exists",
    )
    ap.add_argument(
        "--edge",
        action="store_true",
        help="cover the outermost interval, between the last two nodes, by "
        "the same two-node rule. A covering built on half points stops half a "
        "grid step short of the boundary, and the boundary is where a "
        "free-boundary condition is read.",
    )
    ap.add_argument(
        "--adapt",
        action="store_true",
        help="give each node its own radial resolution, coarse where the "
        "bound is set by the reconstruction rather than by the enclosure",
    )
    ap.add_argument(
        "--adapt-from",
        default=None,
        metavar="FILE",
        help="read that resolution from a measurement instead of from the "
        "thresholds built in: the output of gen/nrad_profile.py, whose lines "
        "'node N: Mx' say how much refining node N still buys",
    )
    ap.add_argument(
        "--shear",
        action="store_true",
        help="carry the flux functions the Mercier criterion needs beside the "
        "angular integrands: the shear, the current gradient and the pressure "
        "gradient, read off the free-radius reconstruction",
    )
    ap.add_argument(
        "--nrad",
        type=int,
        default=8,
        help="radial cells per node interval",
    )
    ap.add_argument("--nodes", type=int, default=6)
    ap.add_argument(
        "--node",
        type=int,
        default=None,
        help="certify this single full-grid node instead of a spread of them",
    )
    ap.add_argument("--nu", type=int, default=8)
    ap.add_argument("--nv", type=int, default=4)
    ap.add_argument(
        "--slack",
        type=float,
        default=1.5,
        help="margin over the float reference for a point certificate; a cell "
        "certificate takes its bounds from --tighten instead",
    )
    ap.add_argument(
        "--stream-defect",
        action="store_true",
        help="carry the defect of the Boozer stream function: how far its "
        "angular derivatives are from the covariant components, and the "
        "surface current that has to vanish for any such function to exist",
    )
    ap.add_argument(
        "--boozer",
        default=None,
        metavar="M,N",
        help="carry the integrand whose angular integral is the (M, N) "
        "harmonic of |B| in the Boozer angles, with the Jacobian of the angle "
        "map, computed from the stream function the certificate carries",
    )
    ap.add_argument(
        "--covariant",
        default=None,
        metavar="M,N",
        help="carry the covariant components against cos(M u - N v): B_u, "
        "B_v and the surface current, whose integrals are the Fourier "
        "coefficients the Boozer stream function is built from",
    )
    ap.add_argument(
        "--covariant-sin",
        default=None,
        metavar="M,N",
        help="the same three against sin(M u - N v)",
    )
    ap.add_argument(
        "--harmonic",
        default=None,
        metavar="M,N",
        help="multiply each residual component by cos(M u - N v), so that "
        "its integral over the surface is the resonant harmonic at that mode",
    )
    ap.add_argument(
        "--coefbox",
        default=None,
        metavar="BLOCK,ROW,MODE,HALF",
        help="vary a coefficient instead of the toroidal angle: the cells "
        "range over that coefficient and the poloidal angle, so a floor "
        "verdict excludes every field whose coefficient lies in the box "
        "rather than the one field the certificate names. BLOCK is rmnc, "
        "zmns or lmns, ROW is 0, 1 or 2 within the node's stencil, and HALF "
        "is the half-width as a fraction of the coefficient.",
    )
    ap.add_argument(
        "--slot3",
        type=int,
        default=None,
        metavar="W",
        help="carry a third varied slot in the file, so that a tightened "
        "certificate is checked by check_ccert3 and its verdict holds at "
        "every point of a cell in three coordinates at once",
    )
    ap.add_argument(
        "--dw3",
        type=float,
        default=None,
        help="half-width of the third slot in radians, default pi so that "
        "one cell spans the whole toroidal angle",
    )
    ap.add_argument(
        "--slots",
        default="1 2",
        help="the two input slots a cell ranges over, 1 and 2 being the "
        "poloidal and toroidal angle",
    )
    ap.add_argument(
        "--mercier",
        choices=["a", "b"],
        default=None,
        help="carry the Mercier integrands: a gives tpp, tbb and tjb, b "
        "gives tjj beside the Jacobian and the square field",
    )
    ap.add_argument(
        "--terms",
        action="store_true",
        help="carry the three terms the residual is the difference of instead "
        "of the residual itself, so that how much they cancel is a certified "
        "number rather than a remark. A term far below the others is one the "
        "bound does not answer to.",
    )
    ap.add_argument(
        "--geometry",
        action="store_true",
        help="carry the integrands of the flux-surface averages instead of "
        "the residual: the Jacobian, the Jacobian-weighted square field, and "
        "the covariant B_u whose average is the enclosed toroidal current",
    )
    ap.add_argument(
        "--lower",
        action="store_true",
        help="claim lower bounds instead of upper ones: every point carries "
        "a component at least this large, which the checker reads with "
        "--lower as a proof that the field is not in force balance",
    )
    ap.add_argument(
        "--perturb",
        default=None,
        metavar="[BLOCK,]J,K,REL",
        help="scale one coefficient by 1 + REL before certifying: surface J, "
        "mode K, of BLOCK (rmnc, zmns or lmns; rmnc by default). A "
        "certificate of the unperturbed bounds then has to come out INVALID, "
        "which is what says the check is sensitive to the physics and not "
        "only to the arithmetic.",
    )
    ap.add_argument(
        "--force-lasym",
        action="store_true",
        help="run a stellarator-symmetric wout through the antisymmetric "
        "reconstruction with every antisymmetric coefficient zero. The result "
        "has to reproduce the symmetric run exactly.",
    )
    ap.add_argument(
        "--prec",
        type=int,
        default=53,
        help="working precision of the interval arithmetic in bits",
    )
    a = ap.parse_args()

    if a.radial:
        a.cells = True
    if (a.geometry or a.mercier or a.shear or a.covariant
            or a.covariant_sin or a.stream_defect or a.boozer
            or a.terms) and not a.cells:
        msg = "these outputs carry integrands, so they need --cells"
        raise SystemExit(msg)
    if a.terms and (a.axis or a.edge):
        msg = ("the innermost and outermost intervals are reconstructed from "
               "two nodes rather than through the Hermite, and --terms reads "
               "the Hermite path")
        raise SystemExit(msg)
    if a.surface and not a.cells:
        msg = "--surface widens cells, so it needs --cells"
        raise SystemExit(msg)
    w = Wout(a.wout)
    if a.perturb is not None:
        parts = a.perturb.split(",")
        block = "rmnc" if len(parts) == 3 else parts[0]
        pj, pk, prel = parts[-3:]
        arr = getattr(w, block)
        arr[int(pj), int(pk)] *= 1.0 + float(prel)
        print(f"perturbed {block}[{pj},{pk}] by {float(prel):+.3%}")
    if w.profile == "PEDESTAL_OFF":
        # a nonpositive width switches the tanh term off, and what remains is
        # the sixteen-term polynomial backbone
        am = np.zeros(21)
        am[0:16] = w.am[0:16]
        w.am = am
        w.profile = "POWER"
        print("pedestal with a nonpositive width: only the polynomial remains")
    # A radial covering may cross a knot of a piecewise profile, in which case
    # no single piece describes the whole range. The pieces are kept here and
    # the covering is split at the knots below, so each node block carries the
    # cubic of the piece its cells lie in.
    if a.radial and w.profile in ("SPLINE", "AKIMA", "SEGMENT"):
        keep = w.aux_s >= 0
        xx, yy = w.aux_s[keep], w.aux_f[keep]
        kind = w.profile
        if kind == "SPLINE":
            y2 = spline_second_derivatives(xx, yy)
            pscale = w.pres_half[1] / spline_eval(xx, yy, y2, w.s_half[1])

            def piece(s):
                return spline_piece(xx, yy, y2, s)
        elif kind == "AKIMA":
            pscale = w.pres_half[1] / akima_eval(xx, yy, w.s_half[1])

            def piece(s):
                return akima_piece(xx, yy, s)
        else:
            k0, v0, sl0 = line_segment_piece(xx, yy, w.s_half[1])
            pscale = w.pres_half[1] / (v0 + (w.s_half[1] - k0) * sl0)

            def piece(s):
                knot, val, slope = line_segment_piece(xx, yy, s)
                return knot, val, slope, 0.0, 0.0

        # The calibration is bound as a default argument rather than left to
        # the enclosing scope. A closure captures the variable, so a later
        # assignment to a name this body reads would silently rescale every
        # pressure piece the covering writes.
        def piece_am(s, pscale=pscale):
            knot, c0, c1, c2, c3 = piece(s)
            am = np.zeros(21)
            am[0:4] = pscale * np.array([c0, c1, c2, c3])
            am[4] = knot
            return am

        w.knots = [float(x) for x in xx]
        w.piece_am = piece_am
        w.am = piece_am(float(w.s_full[w.ns // 2]))
        w.profile = "CUBIC"
        print(f"{kind.lower()} pressure carried piece by piece, "
              f"{len(w.knots)} knots, scale {pscale:.9f}")

    if w.profile == "SEGMENT":
        if a.node is None:
            msg = "a line_segment pressure is resolved per node, so it needs --node"
            raise SystemExit(msg)
        keep = w.aux_s >= 0
        xx, yy = w.aux_s[keep], w.aux_f[keep]
        k0, v0, sl0 = line_segment_piece(xx, yy, w.s_half[1])
        ref = v0 + (w.s_half[1] - k0) * sl0
        scale = w.pres_half[1] / ref
        knot, val, slope = line_segment_piece(xx, yy, w.s_full[a.node])
        w.am = np.zeros(21)
        w.am[0] = scale * val
        w.am[1] = scale * slope
        w.am[4] = knot
        w.profile = "CUBIC"
        print(
            f"line_segment pressure resolved at s={w.s_full[a.node]:.6f}: knot "
            f"{knot:.6f}, slope {scale * slope:.9e}, scale {scale:.9f}"
        )
    if w.profile == "AKIMA":
        if a.node is None:
            msg = "a spline pressure is resolved per node, so it needs --node"
            raise SystemExit(msg)
        keep = w.aux_s >= 0
        xx, yy = w.aux_s[keep], w.aux_f[keep]
        scale = w.pres_half[1] / akima_eval(xx, yy, w.s_half[1])
        knot, c0, c1, c2, c3 = akima_piece(xx, yy, w.s_full[a.node])
        w.am = np.zeros(21)
        w.am[0:4] = scale * np.array([c0, c1, c2, c3])
        w.am[4] = knot
        w.profile = "CUBIC"
        print(
            f"akima_spline pressure resolved at s={w.s_full[a.node]:.6f}: knot "
            f"{knot:.6f}, scale {scale:.9f}"
        )
    if w.profile == "SPLINE":
        if a.node is None:
            msg = "a spline pressure is resolved per node, so it needs --node"
            raise SystemExit(msg)
        keep = w.aux_s >= 0
        xx, yy = w.aux_s[keep], w.aux_f[keep]
        y2 = spline_second_derivatives(xx, yy)
        # the scale VMEC applies, read off the half-grid pressure it stored
        scale = w.pres_half[1] / spline_eval(xx, yy, y2, w.s_half[1])
        knot, c0, c1, c2, c3 = spline_piece(xx, yy, y2, w.s_full[a.node])
        w.am = np.zeros(21)
        w.am[0:4] = scale * np.array([c0, c1, c2, c3])
        w.am[4] = knot
        w.profile = "CUBIC"
        print(
            f"spline pressure resolved at s={w.s_full[a.node]:.6f}: knot "
            f"{knot:.6f}, scale {scale:.9f}"
        )
    if a.force_lasym and not w.lasym:
        w.lasym = True
        w.rmns = np.zeros_like(w.rmnc)
        w.zmnc = np.zeros_like(w.zmns)
        w.lmnc = np.zeros_like(w.lmns)
    K = len(w.xm)
    phip = float(w.phips[1])
    nfp = 1
    if (w.xn != 0).any():
        nfp = int(np.gcd.reduce(np.abs(w.xn[w.xn != 0])))
    three_d = (w.xn != 0).any()
    nv = a.nv if three_d else 1

    # certified nodes: interior full-grid nodes with both neighbors off the
    # axis, evenly spread
    # the innermost interval is covered from node 1, whose two half points are
    # the first two of the grid; the outermost from node ns-2, whose two nodes
    # are the last two
    lo, hi = (1 if a.axis else 2), w.ns - 2
    if a.edge and a.node is None:
        a.node = w.ns - 2
    if a.node is not None:
        if not lo <= a.node <= hi:
            msg = f"--node must lie in [{lo}, {hi}]"
            raise SystemExit(msg)
        idx = np.array([a.node])
    else:
        idx = np.unique(np.linspace(lo, hi, a.nodes).astype(int))
    # angles: exact doubles
    us = [float(2 * np.pi * k / a.nu) for k in range(a.nu)]
    # Sample planes sit inside one field period; a surface covering has to
    # reach the whole toroidal angle, since nothing here proves the
    # reconstruction repeats from one period to the next.
    period = 1 if a.surface else nfp
    vs = [float(2 * np.pi * k / (period * nv)) for k in range(nv)]
    angles = [(u, v) for u in us for v in vs]

    if a.radial and (a.geometry or a.shear):
        # cells over the angles at a fixed radius, with the reconstruction
        # taken off the grid so that a radial derivative exists to integrate
        coarse = angles[:: max(1, len(angles) // 64)]
        scale = max(
            abs(residual_ref(w, j, u, v, phip)[3]) for j in idx for u, v in coarse
        )
        write_ccert(a, w, K, phip, idx, us, vs, nv, three_d)
        print(f"reference B^2 scale {scale:.3e}")
        return

    if a.radial:
        coarse = angles[:: max(1, len(angles) // 64)]
        # the float reference reads the half-grid rule, which divides by
        # sqrt(s) at the axis, so the innermost interval takes its scale from
        # the first node where that rule is defined
        ref_nodes = [j for j in idx if j >= 2] or [2]
        scale = max(
            abs(residual_ref(w, j, u, v, phip)[3])
            for j in ref_nodes for u, v in coarse
        )
        write_rcert(a, w, K, phip, idx, us, vs[0])
        print(f"reference B^2 scale {scale:.3e}")
        return

    if a.coefbox is not None:
        if a.node is None:
            msg = "a coefficient box is written for one node, so it needs --node"
            raise SystemExit(msg)
        write_coefbox(a, w, K, phip, int(idx[0]), us, vs[0])
        return

    if a.cells:
        # the field-energy scale the bounds are read against, from a coarse
        # subset of the angles: the cell bounds themselves come from the
        # checker, so the reference is needed for scale only
        coarse = angles[:: max(1, len(angles) // 64)]
        scale = max(
            abs(residual_ref(w, j, u, v, phip)[3]) for j in idx for u, v in coarse
        )
        write_ccert(a, w, K, phip, idx, us, vs, nv, three_d)
        print(f"reference B^2 scale {scale:.3e}")
        return

    # choose eps from the float reference
    worst = np.zeros(3)
    scale = 0.0
    per_node = []
    hm, hn = (0.0, 0.0)
    if a.harmonic:
        hm, hn = (float(x) for x in a.harmonic.split(","))
    for j in idx:
        mx = np.zeros(3)
        for u, v in angles:
            rs, ru, rv_, B2 = residual_ref(w, j, u, v, phip)
            if a.harmonic:
                k = np.cos(hm * u - hn * v)
                rs, ru, rv_ = rs * k, ru * k, rv_ * k
            mx = np.maximum(mx, np.abs([rs, ru, rv_]))
            scale = max(scale, abs(B2))
        per_node.append((j, w.s_full[j], mx))
        worst = np.maximum(worst, mx)
    # Floor: interval evaluation carries genuine rounding width, so a claimed
    # bound must sit above it. 1e-10 of the field-energy scale is far above
    # the enclosure width of the evaluation and far below any physical residual
    # of interest.
    if a.lower:
        # every point has to carry a component at least eps, so the claim is
        # set below the smallest such component over the certified points
        floor = min(
            max(abs(v) for v in residual_ref(w, j, u, v_, phip)[:3])
            for j in idx
            for u, v_ in angles
        )
        eps = np.full(3, 0.5 * floor)
    else:
        eps = np.maximum(worst * a.slack, 1e-10 * scale)

    lines = []
    P = lines.append
    P("STELLAROCQ-CERT 6")
    P(f"PREC {a.prec}")
    P(f"LASYM {1 if w.lasym else 0}")
    P(f"PROFILE {w.profile}")
    P(f"SLOTS {a.slots}")
    P("OUTPUT " + output_line(a))
    P(f"MODES {K}")
    for m, n in zip(w.xm, w.xn, strict=True):
        P(f"{m} {n}")
    P("PHIP {} {}".format(*dyadic(phip)))
    P("AM 21")
    for j in range(21):
        am_j = w.am[j] if j < len(w.am) else 0.0
        P("{} {}".format(*dyadic(am_j)))
    for tag, e in zip(("EPS_S", "EPS_U", "EPS_V"), eps, strict=True):
        P("{} {} {}".format(tag, *dyadic(e)))
    P(f"NANGLES {len(angles)}")
    for u, v in angles:
        P("{} {} {} {}".format(*dyadic(u), *dyadic(v)))
    P(f"NNODES {len(idx)}")
    for j in idx:
        P("NODE")
        P("S {} {}".format(*dyadic(w.s_full[j])))
        P("SNODES " + " ".join("{} {}".format(*dyadic(x)) for x in w.s_full[j - 1 : j + 2]))
        P("SHALF " + " ".join("{} {}".format(*dyadic(x)) for x in w.s_half[j : j + 2]))
        P("IOTA " + " ".join("{} {}".format(*dyadic(x)) for x in w.iotas[j : j + 2]))
        blocks = [
            ("RNODES", w.rmnc[j - 1 : j + 2]),
            ("ZNODES", w.zmns[j - 1 : j + 2]),
            ("LHALF", w.lmns[j : j + 2]),
        ]
        if w.lasym:
            blocks += [
                ("RNODES_A", w.rmns[j - 1 : j + 2]),
                ("ZNODES_A", w.zmnc[j - 1 : j + 2]),
                ("LHALF_A", w.lmnc[j : j + 2]),
            ]
        for tag, M in blocks:
            P(tag)
            for row in M:
                P(" ".join("{} {}".format(*dyadic(x)) for x in row))
    pathlib.Path(a.out).write_text("\n".join(lines) + "\n")

    print(
        f"wrote {a.out}: {len(idx)} nodes x {len(angles)} angles = "
        f"{len(idx) * len(angles)} points, K={K}"
    )
    if a.lower:
        print(
            f"claimed floor (mu0-scaled, Pa*mu0): every point carries a "
            f"component at least {eps[0]:.3e}"
        )
    else:
        print(
            f"claimed bounds (mu0-scaled, Pa*mu0):  "
            f"r_s {eps[0]:.3e}  r_u {eps[1]:.3e}  r_v {eps[2]:.3e}"
        )
    print(
        f"reference B^2 scale {scale:.3e}  ->  normalized r_s bound "
        f"{eps[0] / scale:.3e}"
    )
    for j, s, mx in per_node:
        print(f"  node {j:3d}  s={s:.4f}  |r|max = {mx[0]:.3e} {mx[1]:.3e} {mx[2]:.3e}")


if __name__ == "__main__":
    main()
