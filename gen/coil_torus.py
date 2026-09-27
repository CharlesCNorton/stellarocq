"""The angle between a coil field and a torus, bounded over the whole torus.

A torus given by Fourier series in two angles,

    R(u, v) = sum Rc_mn cos(m u - n v),   Z(u, v) = sum Zs_mn sin(m u - n v),

v the geometric toroidal angle, is invariant under the field-line flow of a
field B exactly when B is tangent to it. This file writes the certificate
theories/BoxCell.v establishes for Physics.RCoil: the sine of the angle between
B and the torus, B.n / (|B| |n|) with n = x_u x x_v, at every point of the torus,
B the trapezoidal Biot-Savart rule of a coil set on its quadrature points (how
simsopt's BiotSavart evaluates a coil). Each source point enters as its position
and its weighted tangent mu0 I gamma'(t) dt / (4 pi), both exact doubles.

  python gen/coil_torus.py probe TORUS.npz COILS.npz [--nu 64 --nv 320]
  python gen/coil_torus.py cert  TORUS.npz COILS.npz OUT --nu 256 --nv 1280
  main --bt-tighten OUT OUT_t && main --bt OUT_t
  python gen/coil_torus.py grid  TORUS.npz COILS.npz OUT --nu 96 --nv 480
  main --bp-tighten OUT OUT_t && main --bp OUT_t
  python gen/coil_torus.py grid  TORUS.npz COILS.npz OUT --nu 96 --nv 480 --ceiling C
  main --bp OUT

The covering bounds the sine at every point of the torus, which Taylor cells of
the second order can reach only for a sine far above what an accurate torus
has: a cell's bound carries its size squared times the second derivatives of
terms that cancel in the sine. The grid bounds it at every point of a grid,
one evaluation each.

TORUS.npz holds `modes` (pairs m n, n in units of the geometric angle), `Rc` and
`Zs`; COILS.npz holds `points` and `tangents`, P by 3 each. The cells tile the
whole torus, u and v each over [0, 2 pi), since the rounded source points need
not repeat exactly from one field period to the next.
"""

import argparse
import math
import pathlib
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from forced_sheet import dyadic53  # noqa: E402
from free_boundary import tile_period  # noqa: E402
from make_cert import ANGLE_EXP  # noqa: E402


def load(torus, coils):
    t = np.load(torus)
    c = np.load(coils)
    modes = [(int(m), int(n)) for m, n in np.asarray(t["modes"])]
    return modes, np.asarray(t["Rc"], float), np.asarray(t["Zs"], float), \
        np.asarray(c["points"], float), np.asarray(c["tangents"], float)


def surface(modes, Rc, Zs, u, v):
    """x, x_u, x_v of the torus at arrays of angles."""
    m = np.array([a for a, _ in modes], float)
    n = np.array([b for _, b in modes], float)
    ang = m[:, None] * u[None] - n[:, None] * v[None]
    C, S = np.cos(ang), np.sin(ang)
    R = Rc @ C
    Ru = (-m * Rc) @ S
    Rv = (n * Rc) @ S
    Z = Zs @ S
    Zu = (m * Zs) @ C
    Zv = (-n * Zs) @ C
    cv, sv = np.cos(v), np.sin(v)
    x = np.stack([R * cv, R * sv, Z], -1)
    xu = np.stack([Ru * cv, Ru * sv, Zu], -1)
    xv = np.stack([Rv * cv - R * sv, Rv * sv + R * cv, Zv], -1)
    return x, xu, xv


def field(points, tangents, x, chunk=4096):
    """The trapezoidal Biot-Savart sum at points x, as the certificate reads it."""
    out = np.zeros_like(x)
    for i in range(0, len(x), chunk):
        r = x[i:i + chunk, None, :] - points[None]
        r2 = np.sum(r * r, -1)
        r3 = r2 * np.sqrt(r2)
        out[i:i + chunk] = np.sum(np.cross(tangents[None], r) / r3[..., None], 1)
    return out


def sine(modes, Rc, Zs, points, tangents, u, v):
    x, xu, xv = surface(modes, Rc, Zs, u, v)
    n = np.cross(xu, xv)
    B = field(points, tangents, x)
    return np.sum(B * n, -1) / np.sqrt(np.sum(B * B, -1) * np.sum(n * n, -1))


def cmd_probe(a):
    modes, Rc, Zs, P, T = load(a.torus, a.coils)
    us = 2 * np.pi * (np.arange(a.nu) + 0.5) / a.nu
    vs = 2 * np.pi * (np.arange(a.nv) + 0.5) / a.nv
    U, V = np.meshgrid(us, vs)
    s = sine(modes, Rc, Zs, P, T, U.ravel(), V.ravel()).reshape(U.shape)
    su = np.gradient(s, us, axis=1)
    sv = np.gradient(s, vs, axis=0)
    k = np.unravel_index(np.abs(s).argmax(), s.shape)
    print(f"{len(modes)} modes, {len(P)} source points; max |sine| {np.abs(s).max():.3e} at "
          f"u {us[k[1]]:.3f} v {vs[k[0]]:.4f}, rms {np.sqrt(np.mean(s ** 2)):.3e}; "
          f"max |d_u| {np.abs(su).max():.2e}, |d_v| {np.abs(sv).max():.2e}")


def header(modes, Rc, Zs, P, T):
    """The lines of a certificate up to COMP: the torus in the first node row
    of the R and Z blocks, the source points after the state, the angles on
    the fixed grid of 2^ANGLE_EXP."""
    K = len(modes)
    st = [(0, 0, 0)] * 32
    st[1] = (0, ANGLE_EXP, 0)
    st[2] = (0, ANGLE_EXP, 0)
    rows = lambda c: [dyadic53(x) + (0,) for x in c] + [(0, 0, 0)] * (2 * K)  # noqa: E731
    st += rows(Rc) + rows(Zs) + [(0, 0, 0)] * (2 * K)
    for p, t in zip(P, T, strict=True):
        st += [dyadic53(x) + (0,) for x in (*p, *t)]
    assert len(st) == 32 + 8 * K + 6 * len(P)
    L = ["PREC 53", "LASYM 0", "PROFILE POWER", f"OUTPUT coil {len(P)}", f"MODES {K}"]
    L += [f"{m} {n}" for m, n in modes]
    L += [f"NSLOTS {len(st)}", "STATE"] + [f"{m} {e} {d}" for m, e, d in st]
    L += ["SLOTS 1 2", "COMP 0"]
    return L


def ceiling_dyadic(x):
    """The least N 2^q with N below 2^53 that is at least x > 0."""
    q = math.floor(math.log2(x)) - 52
    N = math.ceil(Fraction(x) / Fraction(2) ** q)
    assert N * Fraction(2) ** q >= Fraction(x) and N < 2**53
    return N, q


def cmd_grid(a):
    """Point certificates of the sine at every point of an nu by nv grid of the
    torus, u and v each over [0, 2 pi): `main --bp-tighten` sets each point's
    ceiling and `main --bp` establishes them (BoxCell.check_bpcert_correct)."""
    modes, Rc, Zs, P, T = load(a.torus, a.coils)
    L = ["STELLAROCQ-BPCERT"] + header(modes, Rc, Zs, P, T)
    pts = [(round(2 * np.pi * i / a.nu / 2.0**ANGLE_EXP),
            round(2 * np.pi * j / a.nv / 2.0**ANGLE_EXP))
           for j in range(a.nv) for i in range(a.nu)]
    k, K = (int(x) for x in a.shard.split("/"))
    pts = pts[k::K]
    N, q = ceiling_dyadic(a.ceiling) if a.ceiling else (1, 0)
    L += [f"POINTS {len(pts)}"] + [f"{mu} {mv} {N} {q} 0" for mu, mv in pts]
    pathlib.Path(a.out).write_text("\n".join(L) + "\n")
    print(f"wrote {a.out}: {len(modes)} modes, {len(P)} source points, {len(pts)} points")


def cmd_cert(a):
    modes, Rc, Zs, P, T = load(a.torus, a.coils)
    ums, du = tile_period(2.0 * np.pi, a.nu, ANGLE_EXP)
    vms, dv = tile_period(2.0 * np.pi, a.nv, ANGLE_EXP)
    L = ["STELLAROCQ-BTCERT"] + header(modes, Rc, Zs, P, T)
    L += [f"HALF {du} {dv}", f"GRID 0 0 {a.nu} {a.nv} 1", f"CELLS {a.nu * a.nv}"]
    for mv in vms:
        for mu in ums:
            L.append(f"{mu} {mv} 1 0 1 0 1 0 1 0 1 0")
    pathlib.Path(a.out).write_text("\n".join(L) + "\n")
    print(f"wrote {a.out}: {len(modes)} modes, {len(P)} source points, "
          f"{a.nu} by {a.nv} cells")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, fn in (("probe", cmd_probe), ("cert", cmd_cert), ("grid", cmd_grid)):
        s = sub.add_parser(name)
        s.add_argument("torus")
        s.add_argument("coils")
        if name in ("cert", "grid"):
            s.add_argument("out")
        s.add_argument("--nu", type=int, default=64)
        s.add_argument("--nv", type=int, default=320)
        if name == "grid":
            s.add_argument("--shard", default="0/1", metavar="K/N",
                           help="every N-th point from the K-th, for runs side by side")
            s.add_argument("--ceiling", type=float, default=None,
                           help="claim |sine| at most this at every point, which "
                           "main --bp establishes without --bp-tighten")
        s.set_defaults(fn=fn)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
