"""Invariant tori of the W7-X coil field, from one field line each.

The coil set is simsopt's W7-X standard configuration: the seven base curves of
`simsopt.configs.get_w7x_data` carried by the five-fold and stellarator
symmetries, five non-planar coil types at 1.62 MA and the planar coils off, each
coil the trapezoidal Biot-Savart rule on its 96 quadrature points. Field lines
are followed in cylindrical coordinates with the toroidal angle as time,

    dR/dphi = R B_R / B_phi,   dZ/dphi = R B_Z / B_phi,

by an eighth-order Runge-Kutta method at a relative tolerance of 1e-13.

Two kinds of torus. A flux surface around the magnetic axis (--start D): the
axis at phi = 0 is the fixed point of the map over one field period on the
midplane of symmetry, and the line starts D outboard of it. A surface of the
5/5 island chain around its O-point (--island D): the O-point is the fixed point
of the map over one full turn on the outboard midplane where that map is
elliptic, and the line starts D outboard of it. Either way the line is followed
through many periods of the map (a field period, or a full turn), the weighted
Birkhoff average (Das, Sander, Saiki and Yorke 2017) of its advance around the
centre is the rotation number per period, and of its crossings against
e^{-i k theta} the Fourier coefficients of the invariant curve at phi = 0 as a
function of the angle that conjugates the map to a rotation. The torus over a
period is that curve carried by the flow,
K(theta, phi) = flow_{0 -> phi}(curve(theta - omega phi)), resampled onto a grid
and written as R = sum Rc cos(m theta - n phi), Z = sum Zs sin(m theta - n phi),
the stellarator-symmetric series gen/coil_torus.py certifies; n runs over
multiples of five for a flux surface and over every integer for an island.

  python gen/w7x_torus.py OUTDIR --start 0.2 [--periods 2000 --mmax 24 --nmax 12]
  python gen/w7x_torus.py OUTDIR --island 0.01 [--periods 1000 --mmax 12 --nmax 60]

writes OUTDIR/torus_<kind>_<D>.npz (modes, Rc, Zs, the rotation number, the
centre and the orbit) and OUTDIR/coils_w7x.npz (every quadrature point and its
weighted tangent mu0 I gamma'(t) / (4 pi N), as gen/coil_torus.py reads them).
Needs simsopt and scipy.
"""

import argparse
import pathlib
import time
import warnings

import numpy as np
from scipy.integrate import solve_ivp

NFP = 5


def coils():
    from simsopt.configs import get_w7x_data
    from simsopt.field import coils_via_symmetries

    with warnings.catch_warnings():
        warnings.simplefilter("ignore", DeprecationWarning)
        curves, currents, _ = get_w7x_data()
    return coils_via_symmetries(curves, currents, NFP, True)


class Lines:
    """The field-line equations of a simsopt field at one point at a time."""

    def __init__(self, cs):
        from simsopt.field import BiotSavart

        self.coils = cs
        self.bs = BiotSavart(cs)

    def rhs(self, phi, y):
        R, Z = y
        c, s = np.cos(phi), np.sin(phi)
        self.bs.set_points(np.array([[R * c, R * s, Z]]))
        Bx, By, Bz = self.bs.B()[0]
        BR = Bx * c + By * s
        Bp = -Bx * s + By * c
        return [R * BR / Bp, R * Bz / Bp]

    def follow(self, y0, phi0, phi1, dense=False):
        return solve_ivp(self.rhs, (phi0, phi1), y0, method="DOP853", rtol=1e-13,
                         atol=1e-13, dense_output=dense)


def weights(n):
    """The bump weights of the weighted Birkhoff average, normalized."""
    t = (np.arange(n) + 0.5) / n
    w = np.exp(-1.0 / (t * (1.0 - t)))
    return w / w.sum()


def fixed_point(L, R, period):
    """A fixed point of the map over `period` on or near the midplane, by
    Newton's method from (R, 0), and the trace of the map's Jacobian there."""
    y = np.array([R, 0.0])
    for _ in range(12):
        f = L.follow(y, 0.0, period).y[:, -1] - y
        h = 1e-7
        g1 = L.follow(y + [h, 0.0], 0.0, period).y[:, -1] - (y + [h, 0.0])
        g2 = L.follow(y + [0.0, h], 0.0, period).y[:, -1] - (y + [0.0, h])
        J = np.column_stack([(g1 - f) / h, (g2 - f) / h])
        y = y + np.linalg.solve(J, -f)
        if np.abs(f).max() < 1e-13:
            break
    return y, float(np.abs(f).max()), float(np.trace(J + np.eye(2)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--start", type=float, help="distance outboard of the axis, m")
    g.add_argument("--island", type=float, help="distance outboard of the O-point, m")
    ap.add_argument("--opoint", type=float, default=6.235,
                    help="where Newton's method starts for the O-point")
    ap.add_argument("--periods", type=int, default=2000)
    ap.add_argument("--modes", type=int, default=48, help="of the curve at phi = 0")
    ap.add_argument("--nth", type=int, default=96)
    ap.add_argument("--nph", type=int, default=48)
    ap.add_argument("--mmax", type=int, default=24)
    ap.add_argument("--nmax", type=int, default=12)
    a = ap.parse_args()
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    L = Lines(coils())
    island = a.island is not None
    period = 2 * np.pi if island else 2 * np.pi / NFP
    step = 1 if island else NFP        # the toroidal mode numbers the torus carries
    c0, res, tr = fixed_point(L, a.opoint if island else 5.95, period)
    kind = "island" if island else "surface"
    print(f"centre at R = {c0[0]:.12f}, Z = {c0[1]:+.2e} (residual {res:.1e}, trace of the "
          f"map's Jacobian {tr:+.6f}, {'elliptic' if abs(tr) < 2 else 'hyperbolic'})", flush=True)
    if island and abs(tr) >= 2:
        raise SystemExit("the fixed point is not an O-point")
    D = a.island if island else a.start
    y = c0 + np.array([D, 0.0])
    pts = [y.copy()]
    for k in range(a.periods):
        y = L.follow(y, k * period, (k + 1) * period).y[:, -1]
        pts.append(y.copy())
    P = np.array(pts)
    ang = np.unwrap(np.arctan2(P[:, 1] - c0[1], P[:, 0] - c0[0]))
    d = np.diff(ang)
    rho = float(weights(len(d)) @ d) / (2 * np.pi)
    h = len(d) // 2
    r1 = float(weights(h) @ d[:h]) / (2 * np.pi)
    r2 = float(weights(len(d) - h) @ d[h:]) / (2 * np.pi)
    omega = 2 * np.pi * rho / period   # angle advance per radian of phi
    print(f"rotation per period {rho:.15f} (halves {r1:.15f}, {r2:.15f}), "
          f"{omega:.12f} per radian of phi ({time.time() - t0:.0f} s)", flush=True)
    th = 2 * np.pi * rho * np.arange(len(P))
    wP = weights(len(P))
    K = a.modes
    cR = np.array([wP @ (P[:, 0] * np.exp(-1j * k * th)) for k in range(K + 1)])
    cZ = np.array([wP @ (P[:, 1] * np.exp(-1j * k * th)) for k in range(K + 1)])
    wk = np.where(np.arange(K + 1) == 0, 1.0, 2.0)

    def curve(t):
        e = np.exp(1j * np.outer(np.atleast_1d(t), np.arange(K + 1)))
        return np.real(e @ (wk * cR)), np.real(e @ (wk * cZ))

    Rc0, Zc0 = curve(th)
    err = float(np.hypot(Rc0 - P[:, 0], Zc0 - P[:, 1]).max())
    print(f"orbit against the curve: {err:.2e}; |c| at k = {K}: {abs(cR[K]):.1e}, "
          f"{abs(cZ[K]):.1e}", flush=True)
    Nt, Nf = a.nth, a.nph
    ths = 2 * np.pi * np.arange(Nt) / Nt
    phs = period * np.arange(Nf) / Nf
    RR = np.zeros((Nf, Nt))
    ZZ = np.zeros((Nf, Nt))
    for i, t in enumerate(ths):
        R0c, Z0c = curve(t)
        Y = L.follow([R0c[0], Z0c[0]], 0.0, period, dense=True).sol(phs)
        RR[:, i], ZZ[:, i] = Y[0], Y[1]
    # row j holds K(theta_i + omega phi_j, phi_j); shift it back spectrally
    kk = np.fft.fftfreq(Nt, 1.0 / Nt)
    for j, ph in enumerate(phs):
        sh = np.exp(-1j * kk * omega * ph)
        RR[j] = np.real(np.fft.ifft(np.fft.fft(RR[j]) * sh))
        ZZ[j] = np.real(np.fft.ifft(np.fft.fft(ZZ[j]) * sh))
    CR = np.fft.fft2(RR) / (Nf * Nt)
    CZ = np.fft.fft2(ZZ) / (Nf * Nt)
    modes, Rc, Zs, Ri, Zi = [], [], [], [], []
    for m in range(a.mmax + 1):
        for n in range(-a.nmax, a.nmax + 1):
            if m == 0 and n < 0:
                continue
            w = 1.0 if (m == 0 and n == 0) else 2.0
            cr, cz = CR[(-n) % Nf, m % Nt], CZ[(-n) % Nf, m % Nt]
            modes.append((m, n * step))
            Rc.append(w * cr.real)
            Zs.append(-w * cz.imag)
            Ri.append(w * cr.imag)
            Zi.append(w * cz.real)
    modes = np.array(modes)
    Rc, Zs = np.array(Rc), np.array(Zs)
    print(f"torus: {len(modes)} modes; the symmetric series drops at most "
          f"{max(np.abs(Ri).max(), np.abs(Zi).max()):.1e}; largest coefficient at m = {a.mmax}: "
          f"{np.abs(Rc[modes[:, 0] == a.mmax]).max():.1e}, at |n| = {a.nmax * step}: "
          f"{np.abs(Rc[np.abs(modes[:, 1]) == a.nmax * step]).max():.1e} "
          f"({time.time() - t0:.0f} s)", flush=True)
    tag = f"{kind}_{D:.3f}"
    np.savez(out / f"torus_{tag}.npz", modes=modes, Rc=Rc, Zs=Zs, rho=rho, omega=omega,
             centre=c0, orbit=P, cR=cR, cZ=cZ, period=period)
    pts, tans = [], []
    for c in L.coils:
        gm = c.curve.gamma()
        gd = c.curve.gammadash()
        pts.append(gm)
        tans.append(1e-7 * c.current.get_value() * gd / len(gm))
    np.savez(out / "coils_w7x.npz", points=np.concatenate(pts), tangents=np.concatenate(tans))
    print(f"wrote {out}/torus_{tag}.npz and {out}/coils_w7x.npz", flush=True)


if __name__ == "__main__":
    main()
