"""Pressure profile and gradient for every VMEC++ parameterization, from the formulas.

A third independent writing of dp/ds, beside the expression trees of
theories/Physics.v and the float pass of gen/make_cert.py, taken from the
profile definitions and carrying the value as well as the derivative.

VMEC scales every profile by PRES_SCALE, which the wout does not store, so a
profile read from am alone is the input and not the balanced pressure;
Profile.from_wout recovers the scale from the file's own first half-grid
pressure.

  from pressure_ref import Profile
  prof = Profile.from_wout(w)      # w carries pmass_type, am, am_aux_*, pres
  prof.value(s), prof.derivative(s)
"""

import bisect

import numpy as np


def _amj(am, j):
    return float(am[j]) if j < len(am) else 0.0


# ---- the closed forms, value and derivative ---------------------------------

def power_series(am, s, n=21):
    val = sum(_amj(am, j) * s ** j for j in range(n))
    der = sum(j * _amj(am, j) * s ** (j - 1) for j in range(1, n))
    return val, der


def two_power(am, s):
    a, p, q = _amj(am, 0), _amj(am, 1), _amj(am, 2)
    base = 1.0 - s ** p
    val = a * base ** q
    der = -a * p * q * s ** (p - 1) * base ** (q - 1) if (p > 0 and q > 0) else 0.0
    return val, der


def gauss_bumps(am, s):
    """1 plus the two_power_gs Gaussian bumps and its derivative; a zero-amplitude bump is skipped."""
    val, der = 1.0, 0.0
    for j in range(6):
        amp, ctr, wid = _amj(am, 3 + 3 * j), _amj(am, 4 + 3 * j), _amj(am, 5 + 3 * j)
        if amp == 0.0:
            continue
        x = (s - ctr) / wid
        e = np.exp(-x * x)
        val += amp * e
        der += amp * e * (-2.0 * x / wid)
    return val, der


def two_power_gs(am, s):
    v0, d0 = two_power(am, s)
    v1, d1 = gauss_bumps(am, s)
    return v0 * v1, d0 * v1 + v0 * d1


def gauss_trunc(am, s):
    a, w = _amj(am, 0), _amj(am, 1)
    e1 = np.exp(-(1.0 / w) ** 2)
    e = np.exp(-(s / w) ** 2)
    val = a * (e - e1) / (1.0 - e1)
    der = a * e * (-2.0 * s / (w * w)) / (1.0 - e1)
    return val, der


def lorentz(s, a, p, q):
    """One Lorentz factor 1 / (1 + (s / a^2)^p)^q and its derivative."""
    z = s / (a * a)
    base = 1.0 + z ** p
    val = base ** (-q)
    der = (-q * base ** (-q - 1) * p * z ** (p - 1) / (a * a)
           if (p > 0 and q > 0) else 0.0)
    return val, der


def two_lorentz(am, s):
    a0, a1 = _amj(am, 0), _amj(am, 1)
    A, dA = lorentz(s, _amj(am, 2), _amj(am, 3), _amj(am, 4))
    A1, _ = lorentz(1.0, _amj(am, 2), _amj(am, 3), _amj(am, 4))
    B, dB = lorentz(s, _amj(am, 5), _amj(am, 6), _amj(am, 7))
    B1, _ = lorentz(1.0, _amj(am, 5), _amj(am, 6), _amj(am, 7))
    val = a0 * (a1 * (A - A1) / (1.0 - A1) + (1.0 - a1) * (B - B1) / (1.0 - B1))
    der = a0 * (a1 * dA / (1.0 - A1) + (1.0 - a1) * dB / (1.0 - B1))
    return val, der


def pedestal(am, s):
    v, d = power_series(am, s, 16)
    c, w = _amj(am, 18), _amj(am, 19)
    if w <= 0.0:
        return v, d
    t1 = np.tanh(2.0 * (c - np.sqrt(s)) / w)
    te = np.tanh(2.0 * (c - 1.0) / w)
    t0 = np.tanh(2.0 * c / w)
    nn = _amj(am, 17) / (t0 - te)
    val = v + nn * (t1 - te)
    # d/ds tanh(2 (c - sqrt s) / w) = (1 - t1^2) (-1 / (w sqrt s))
    der = d + nn * (1.0 - t1 * t1) * (-1.0 / (w * np.sqrt(s)))
    return val, der


def rational(am, s, nn=10, nd=11):
    nu = sum(_amj(am, j) * s ** j for j in range(nn))
    dnu = sum(j * _amj(am, j) * s ** (j - 1) for j in range(1, nn))
    de = sum(_amj(am, 10 + j) * s ** j for j in range(nd))
    dde = sum(j * _amj(am, 10 + j) * s ** (j - 1) for j in range(1, nd))
    return nu / de, (dnu * de - nu * dde) / (de * de)


# ---- the piecewise forms, through the knots ---------------------------------

def clamped_spline_second_derivatives(x, y):
    """Second derivatives of the cubic spline with quadratic end slopes, by the tridiagonal solve."""
    x, y = np.asarray(x, float), np.asarray(y, float)
    n = len(x)
    h = np.diff(x)

    def quad_slope(i0, i1, i2, at):
        d1 = (y[i1] - y[i0]) / (x[i1] - x[i0])
        d2 = ((y[i2] - y[i1]) / (x[i2] - x[i1]) - d1) / (x[i2] - x[i0])
        return d1 + d2 * (2 * at - x[i0] - x[i1])

    yp1 = quad_slope(0, 1, 2, x[0])
    ypn = quad_slope(n - 3, n - 2, n - 1, x[n - 1])
    # the system for the second derivatives M: sub, diag, sup, rhs
    sub = np.zeros(n)
    dia = np.zeros(n)
    sup = np.zeros(n)
    rhs = np.zeros(n)
    dia[0], sup[0] = 2 * h[0], h[0]
    rhs[0] = 6 * ((y[1] - y[0]) / h[0] - yp1)
    for i in range(1, n - 1):
        sub[i], dia[i], sup[i] = h[i - 1], 2 * (h[i - 1] + h[i]), h[i]
        rhs[i] = 6 * ((y[i + 1] - y[i]) / h[i] - (y[i] - y[i - 1]) / h[i - 1])
    sub[n - 1], dia[n - 1] = h[n - 2], 2 * h[n - 2]
    rhs[n - 1] = 6 * (ypn - (y[n - 1] - y[n - 2]) / h[n - 2])
    # Thomas
    for i in range(1, n):
        f = sub[i] / dia[i - 1]
        dia[i] -= f * sup[i - 1]
        rhs[i] -= f * rhs[i - 1]
    M = np.zeros(n)
    M[n - 1] = rhs[n - 1] / dia[n - 1]
    for i in range(n - 2, -1, -1):
        M[i] = (rhs[i] - sup[i] * M[i + 1]) / dia[i]
    return M


def cubic_spline(x, y, M, s):
    x, y = np.asarray(x, float), np.asarray(y, float)
    s = min(max(s, x[0]), x[-1])
    k = min(max(bisect.bisect_right(x, s) - 1, 0), len(x) - 2)
    h = x[k + 1] - x[k]
    a, b = x[k + 1] - s, s - x[k]
    val = (M[k] * a ** 3 / (6 * h) + M[k + 1] * b ** 3 / (6 * h)
           + (y[k] / h - M[k] * h / 6) * a + (y[k + 1] / h - M[k + 1] * h / 6) * b)
    der = (-M[k] * a ** 2 / (2 * h) + M[k + 1] * b ** 2 / (2 * h)
           - (y[k] / h - M[k] * h / 6) + (y[k + 1] / h - M[k + 1] * h / 6))
    return val, der


def akima(x, y, s):
    """VMEC++ Akima interpolant: two reflected phantom knots per end, quadratic end values, Akima slopes."""
    x, y = list(map(float, x)), list(map(float, y))
    n = len(x)
    if n < 4:
        raise ValueError("an akima profile needs at least four knots")
    # indices -2 .. n+1 stored at offset 2
    o = 2
    X = [0.0] * (n + 4)
    Y = [0.0] * (n + 4)
    for i in range(n):
        X[i + o], Y[i + o] = x[i], y[i]
    X[o - 2] = 2 * x[0] - x[2]
    X[o - 1] = x[0] + x[1] - x[2]
    X[n + o] = x[n - 1] + x[n - 2] - x[n - 3]
    X[n + 1 + o] = 2 * x[n - 1] - x[n - 3]
    m = lambda i: (Y[i + 1 + o] - Y[i + o]) / (X[i + 1 + o] - X[i + o])  # noqa: E731
    # the end values from the quadratics through the end triples
    cl = (m(1) - m(0)) / (x[2] - x[0])
    bl = m(0) - cl * (x[1] - x[0])
    cr = (m(n - 2) - m(n - 3)) / (x[n - 1] - x[n - 3])
    br = m(n - 2) - cr * (x[n - 2] - x[n - 1])
    for f in (-1, -2):
        d = X[f + o] - x[0]
        Y[f + o] = y[0] + bl * d + cl * d * d
    for f in (n, n + 1):
        d = X[f + o] - x[n - 1]
        Y[f + o] = y[n - 1] + br * d + cr * d * d
    M = {i: m(i) for i in range(-2, n + 1)}
    DM = {i: abs(M[i + 1] - M[i]) for i in range(-2, n)}
    T = {}
    for i in range(n):
        den = DM[i] + DM[i - 2]
        if den != 0.0:
            P, Q = DM[i] / den, DM[i - 2] / den
            T[i] = P * M[i - 1] + Q * M[i]
        else:
            T[i] = 0.5 * (M[i - 1] + M[i])
    if not x[0] <= s <= x[-1]:
        raise ValueError(f"s={s} lies outside the akima knots")
    i = max(0, min(n - 2, bisect.bisect_right(x, s) - 1))
    h = x[i + 1] - x[i]
    a, b = y[i], T[i]
    c = (3 * M[i] - T[i + 1] - 2 * T[i]) / h
    d = (T[i + 1] + T[i] - 2 * M[i]) / (h * h)
    t = s - x[i]
    return a + t * (b + t * (c + d * t)), b + t * (2 * c + 3 * d * t)


def line_segment(x, y, s):
    """VMEC++ piecewise linear profile: the segment above each point, flat outside the knots."""
    x, y = list(map(float, x)), list(map(float, y))
    n = len(x)
    i = bisect.bisect_left(x, s)
    if i >= n - 1:
        return y[n - 1], 0.0
    if i == 0:
        return y[0], 0.0
    slope = (y[i + 1] - y[i]) / (x[i + 1] - x[i])
    return y[i] + slope * (s - x[i]), slope


# ---- the profile of a wout --------------------------------------------------

class Profile:
    """One profile, calibrated to the wout's own pressure."""

    def __init__(self, pmass_type, am, aux_s=None, aux_f=None):
        self.kind = (pmass_type or "power_series").strip()
        self.am = np.asarray(am, float)
        self.scale = 1.0
        if self.kind in ("cubic_spline", "akima_spline", "line_segment"):
            keep = np.asarray(aux_s) >= 0
            self.xx = np.asarray(aux_s, float)[keep]
            self.yy = np.asarray(aux_f, float)[keep]
            if self.kind == "cubic_spline":
                self.M = clamped_spline_second_derivatives(self.xx, self.yy)

    def raw(self, s):
        """Value and derivative before the scale."""
        k, am = self.kind, self.am
        if k in ("power_series", ""):
            return power_series(am, s)
        if k == "two_power":
            return two_power(am, s)
        if k == "two_power_gs":
            return two_power_gs(am, s)
        if k == "gauss_trunc":
            return gauss_trunc(am, s)
        if k == "two_lorentz":
            return two_lorentz(am, s)
        if k == "pedestal":
            return pedestal(am, s)
        if k == "rational":
            return rational(am, s)
        if k == "cubic_spline":
            return cubic_spline(self.xx, self.yy, self.M, s)
        if k == "akima_spline":
            return akima(self.xx, self.yy, s)
        if k == "line_segment":
            return line_segment(self.xx, self.yy, s)
        raise ValueError(f"no reference for pmass_type {k!r}")

    def value(self, s):
        return self.scale * self.raw(s)[0]

    def derivative(self, s):
        return self.scale * self.raw(s)[1]

    @classmethod
    def from_wout(cls, w):
        """Profile of a wout, with the scale recovered from pres at the first half point."""
        prof = cls(getattr(w, "pmass_type", ""), w.am,
                   getattr(w, "aux_s", None), getattr(w, "aux_f", None))
        s1 = float(w.s_half[1])
        raw = prof.raw(s1)[0]
        if raw != 0.0 and hasattr(w, "pres_half"):
            prof.scale = float(w.pres_half[1]) / raw
        return prof
