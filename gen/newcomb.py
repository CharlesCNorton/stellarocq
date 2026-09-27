"""Newcomb's condition on a rational surface of a finite-beta equilibrium.

On a surface where iota = n/m, the field lines of a nested-surface field close
after m toroidal turns, and in straight-field-line angles (theta*, v) the
integral of dl/B along the line theta* = alpha + iota v is

    (1 / phip) int_0^{2 pi m} sqrt(g*) dv
      = (2 pi m / phip) sum_p G_{pm, pn} e^{i p m alpha},

G_{jk} the Fourier coefficients of the Jacobian sqrt(g*) of those angles. A
smooth equilibrium with p' != 0 there has the integral independent of alpha
(Newcomb 1959), so G_{m,n} = 0; a certified G_{m,n} != 0 at a certified
p' != 0 on a certified crossing of iota through n/m excludes it.

This writes the certificates of that statement for the reconstruction of a
VMEC++ equilibrium carried into straight-field-line angles: R and Z of the
three nodes around the crossing, transformed to theta* = u + lambda and
truncated to the modes kept, with lambda zero. They are about every state in
a box around it, the free radius ranging over an interval that holds the
crossing for every state of the box:

  harm   Harmonic.harm_correct on OUTPUT newcomb m n, component 0: the torus
         integral of sqrt(g*) cos(m theta* - n v), exactly.
  iota   point certificates of m iota - n: at most -eps at the inner end of
         the interval and at least eps at the outer, so iota crosses n/m in it.
  pp     a point certificate of |mu0 p'| from below over the interval.

  python gen/newcomb.py probe WOUT --m 11 --n 10
  python gen/newcomb.py certs WOUT OUTPREFIX --m 11 --n 10 --rel 1e-8
"""

import argparse
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from forced_sheet import box_block, point  # noqa: E402
from make_cert import (  # noqa: E402
    ANGLE_EXP,
    MU0,
    Wout,
    calibrate_pressure,
    dyadic,
    pprime_ref,
)


def lam_node(w, j, u, v):
    """lambda at full-grid node j: the mean of the two half rows around it."""
    ang = np.multiply.outer(w.xm, u) - np.multiply.outer(w.xn, v)
    lam = 0.5 * (w.lmns[j] + w.lmns[j + 1])
    return np.tensordot(lam, np.sin(ang), 1)


def pest_node(w, j, M, N, nfp, nu=None, nv=None):
    """R and Z of node j on a grid of straight-field-line angles, transformed
    to the cos (R) and sin (Z) series over m <= M, |n| <= N nfp."""
    nu = nu or 4 * (M + 1)
    nv = nv or 4 * (2 * N + 1)
    th = 2 * np.pi * np.arange(nu) / nu
    vv = 2 * np.pi * np.arange(nv) / (nfp * nv)
    lamc = 0.5 * (w.lmns[j] + w.lmns[j + 1])
    xm, xn = w.xm.astype(float), w.xn.astype(float)
    R = np.zeros((nv, nu))
    Zg = np.zeros((nv, nu))
    for b, v in enumerate(vv):
        u = th.copy()
        for _ in range(60):  # u + lambda(u, v) = theta*
            ang = np.multiply.outer(xm, u) - xn[:, None] * v
            f = u + lamc @ np.sin(ang) - th
            fp = 1.0 + (lamc * xm) @ np.cos(ang)
            du = f / fp
            u -= du
            if np.abs(du).max() < 1e-15:
                break
        ang = np.multiply.outer(xm, u) - xn[:, None] * v
        R[b] = w.rmnc[j] @ np.cos(ang)
        Zg[b] = w.zmns[j] @ np.sin(ang)
    modes = [(m, n * nfp) for m in range(M + 1) for n in range(-N, N + 1) if m > 0 or n >= 0]
    TH, VV = np.meshgrid(th, vv)
    rc, zs = [], []
    for m, n in modes:
        a = m * TH - n * VV
        wgt = 1.0 if (m == 0 and n == 0) else 2.0
        rc.append(wgt * np.mean(R * np.cos(a)))
        zs.append(wgt * np.mean(Zg * np.sin(a)))
    rc, zs = np.array(rc), np.array(zs)
    # what the kept modes leave of the grid values
    rec_R = sum(c * np.cos(m * TH - n * VV) for c, (m, n) in zip(rc, modes))
    rec_Z = sum(c * np.sin(m * TH - n * VV) for c, (m, n) in zip(zs, modes))
    err = max(np.abs(rec_R - R).max(), np.abs(rec_Z - Zg).max())
    return modes, rc, zs, err


def rational_node(w, m, n):
    """The node whose half points bracket the crossing of iota through n/m,
    and the crossing, with iota linear between half points."""
    target = n / m
    for j in range(1, w.ns - 2):
        a, b = w.iotas[j], w.iotas[j + 1]
        if (a - target) * (b - target) <= 0 and a != b:
            t = (target - a) / (b - a)
            return j, w.s_half[j] + t * (w.s_half[j + 1] - w.s_half[j])
    raise SystemExit(f"iota does not cross {n}/{m} on the half grid")


def hermite(ya, da, yb, db, sa, sb, s):
    """The cubic Hermite through values and slopes at sa and sb, and its
    slope, as Physics.hermcoef_b writes it."""
    H = sb - sa
    t = (s - sa) / H
    sec = (yb - ya) / H
    al, be = da - sec, db - sec
    h10, h11 = t**3 - 2 * t**2 + t, t**3 - t**2
    g10, g11 = 3 * t**2 - 4 * t + 1, 3 * t**2 - 2 * t
    return ya + t * (yb - ya) + H * (h10 * al + h11 * be), sec + g10 * al + g11 * be


def half_coefs(c_in, c_out, s_a, s_b, s_h, odd):
    ev, ed = 0.5 * (c_in + c_out), (c_out - c_in) / (s_b - s_a)
    qa, qb = c_in / np.sqrt(s_a), c_out / np.sqrt(s_b)
    ov = np.sqrt(s_h) * 0.5 * (qa + qb)
    od = np.sqrt(s_h) * (qb - qa) / (s_b - s_a) + ov / (2.0 * s_h)
    return np.where(odd, ov, ev), np.where(odd, od, ed)


def jacobian_harmonic(w, j, modes, rows_R, rows_Z, s, m, n, nu=128, nv=None, nfp=5):
    """The float torus integral of sqrt(g*) cos(m theta* - n v) at radius s,
    from the three PEST rows of node j."""
    mm = np.array([a for a, _ in modes], float)
    nn = np.array([b for _, b in modes], float)
    odd = (mm % 2) == 1
    sa, sj, sb = w.s_full[j - 1], w.s_full[j], w.s_full[j + 1]
    shm, shp = w.s_half[j], w.s_half[j + 1]
    cRm, dRm = half_coefs(rows_R[0], rows_R[1], sa, sj, shm, odd)
    cRp, dRp = half_coefs(rows_R[1], rows_R[2], sj, sb, shp, odd)
    cZm, dZm = half_coefs(rows_Z[0], rows_Z[1], sa, sj, shm, odd)
    cZp, dZp = half_coefs(rows_Z[1], rows_Z[2], sj, sb, shp, odd)
    cR, cRs = hermite(cRm, dRm, cRp, dRp, shm, shp, s)
    cZ, cZs = hermite(cZm, dZm, cZp, dZp, shm, shp, s)
    nv = nv or 4 * int(np.abs(nn).max() + abs(n) + 1)
    th = 2 * np.pi * np.arange(nu) / nu
    vv = 2 * np.pi * np.arange(nv) / nv
    TH, VV = np.meshgrid(th, vv)
    ang = mm[:, None, None] * TH[None] - nn[:, None, None] * VV[None]
    c, sn = np.cos(ang), np.sin(ang)
    R = np.tensordot(cR, c, 1)
    Ru = np.tensordot(-mm * cR, sn, 1)
    Rs = np.tensordot(cRs, c, 1)
    Zu = np.tensordot(mm * cZ, c, 1)
    Zs = np.tensordot(cZs, sn, 1)
    sg = R * (Ru * Zs - Rs * Zu)
    return float(np.mean(sg * np.cos(m * TH - n * VV))) * 4 * np.pi**2, float(np.mean(sg)) * 4 * np.pi**2


def load(path):
    w = Wout(path)
    calibrate_pressure(w)
    return w


def cmd_probe(a):
    w = load(a.wout)
    j, s_star = rational_node(w, a.m, a.n)
    print(f"iota = {a.n}/{a.m} crosses at s = {s_star:.6f}, node {j} "
          f"(half points {w.s_half[j]:.6f}, {w.s_half[j + 1]:.6f}); "
          f"mu0 p'(s) = {MU0 * pprime_ref(w.profile, w.am, s_star):.6e}")
    for M, N in a.sizes:
        rows = [pest_node(w, jj, M, N, a.nfp) for jj in (j - 1, j, j + 1)]
        modes = rows[0][0]
        err = max(r[3] for r in rows)
        C, mean = jacobian_harmonic(w, j, modes, [r[1] for r in rows], [r[2] for r in rows],
                                    s_star, a.m, a.n, nfp=a.nfp)
        print(f"M {M} N {N}: {len(modes)} modes, transform residual {err:.1e}; "
              f"int sqrt(g*) cos({a.m} th - {a.n} v) = {C:+.6e} (mean {mean:+.6e})")


def write_header(L, w, modes, out, st):
    L.append("PREC 53")
    L.append("LASYM 0")
    L.append(f"PROFILE {w.profile}")
    L.append(f"OUTPUT {out}")
    L.append(f"MODES {len(modes)}")
    L += [f"{m} {n}" for m, n in modes]
    L.append(f"NSLOTS {len(st)}")
    L.append("STATE")
    L += [f"{m} {e} {d}" for m, e, d in st]


def cmd_certs(a):
    w = load(a.wout)
    j, s_star = rational_node(w, a.m, a.n)
    rows = [pest_node(w, jj, a.M, a.N, a.nfp) for jj in (j - 1, j, j + 1)]
    modes = rows[0][0]
    K = len(modes)
    phip = float(w.phips[1])
    shm, shp = w.s_half[j], w.s_half[j + 1]
    iom, iop = float(w.iotas[j]), float(w.iotas[j + 1])
    # the interval of the free radius: the crossing, widened by what the box
    # does to iota, and kept inside the node's half points
    dio = (iop - iom) / (shp - shm)
    ds = (a.rel_iota * max(abs(iom), abs(iop)) * 4 + a.margin) / abs(dio)
    s_lo, s_hi = max(shm, s_star - ds), min(shp, s_star + ds)
    e_s = -60
    s_mid = round(0.5 * (s_lo + s_hi) / 2.0**e_s)
    s_half = int(np.ceil(0.5 * (s_hi - s_lo) / 2.0**e_s)) + 1

    def state(s_slot, iota_rel):
        st = [s_slot, (0, ANGLE_EXP, 0), (0, ANGLE_EXP, 0), point(phip)]
        st += [point(x) for x in w.s_full[j - 1: j + 2]]
        st += [point(shm), point(shp)]
        st += box_block([iom, iop], iota_rel)
        st += [point(w.am[i] if i < len(w.am) else 0.0) for i in range(21)]
        for r in rows:
            st += box_block(r[1], a.rel)
        for r in rows:
            st += box_block(r[2], a.rel)
        st += [(0, 0, 0)] * (2 * K)  # lambda of straight-field-line angles
        assert len(st) == 32 + 8 * K
        return st

    head_box = (s_mid, e_s, s_half)
    lo_pt = (round(s_lo / 2.0**e_s), e_s, 0)
    hi_pt = (round(s_hi / 2.0**e_s), e_s, 0)
    # the harmonic: degree below the grid
    Mmax = max(m for m, _ in modes)
    Nmax = max(abs(n) for _, n in modes)
    Nu = 3 * Mmax + abs(a.m) + 1 + a.grid_margin
    Nv = 3 * Nmax + abs(a.n) + 1 + a.grid_margin
    L = ["STELLAROCQ-HCERT"]
    write_header(L, w, modes, f"newcomb {a.m} {a.n}", state(head_box, a.rel_iota))
    L += ["SLOTS 1 2", "COMP 0", f"GRID {Nu} {Nv}"]
    pathlib.Path(a.out + "_harm.txt").write_text("\n".join(L) + "\n")
    # iota at the two ends, and the pressure gradient over the interval
    for name, pt, mode in (("iota_lo", lo_pt, 3), ("iota_hi", hi_pt, 2)):
        L = ["STELLAROCQ-BPCERT"]
        write_header(L, w, modes, f"iota {a.m} {a.n}", state(pt, a.rel_iota))
        L += ["SLOTS 1 2", "COMP 0", "POINTS 1", f"0 0 1 0 {mode}"]
        pathlib.Path(a.out + f"_{name}.txt").write_text("\n".join(L) + "\n")
    L = ["STELLAROCQ-BPCERT"]
    write_header(L, w, modes, f"newcomb {a.m} {a.n}", state(head_box, a.rel_iota))
    L += ["SLOTS 1 2", "COMP 2", "POINTS 1", "0 0 1 0 1"]
    pathlib.Path(a.out + "_pp.txt").write_text("\n".join(L) + "\n")
    C, mean = jacobian_harmonic(w, j, modes, [r[1] for r in rows], [r[2] for r in rows],
                                s_star, a.m, a.n, nfp=a.nfp)
    print(f"node {j}, crossing at s = {s_star:.8f}, free radius over [{s_lo:.8f}, {s_hi:.8f}]; "
          f"{K} modes, transform residual {max(r[3] for r in rows):.1e}; grid {Nu} x {Nv}; "
          f"float harmonic {C:+.6e}, mu0 p' {MU0 * pprime_ref(w.profile, w.am, s_star):.4e}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("probe")
    p.add_argument("wout")
    p.add_argument("--sizes", type=lambda t: [tuple(int(x) for x in q.split(",")) for q in t.split("/")],
                   default=[(12, 12), (16, 14), (20, 16)])
    c = sub.add_parser("certs")
    c.add_argument("wout")
    c.add_argument("out")
    c.add_argument("--M", type=int, default=24)
    c.add_argument("--N", type=int, default=20)
    c.add_argument("--rel", type=float, default=1e-8,
                   help="half-width of every R and Z coefficient, relative")
    c.add_argument("--rel-iota", type=float, default=1e-8)
    c.add_argument("--margin", type=float, default=1e-9,
                   help="how far past the crossing iota must reach at each end")
    c.add_argument("--grid-margin", type=int, default=2)
    for s in (p, c):
        s.add_argument("--m", type=int, default=11)
        s.add_argument("--n", type=int, default=10)
        s.add_argument("--nfp", type=int, default=5)
    p.set_defaults(fn=cmd_probe)
    c.set_defaults(fn=cmd_certs)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
