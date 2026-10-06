"""Free-boundary balance over the whole plasma boundary, against two vacuum fields.

At a free-boundary equilibrium the total pressure p + B^2/2 is continuous
across the plasma boundary, where outside it is the vacuum magnetic pressure
B_vac^2/2 of the full vacuum field, coils and plasma currents together. VMEC++
computes that field with NESTOR; the virtual-casing field of BIEST gives it
independently as B_coil + B_in - B_ext, with B_ext the field of the external
currents recovered from the plasma-side field B_in.

This file writes the certificate theories/BoxCell.v establishes for the jump

    J(u, v) = (p + B^2/2)_edge - P_vac(u, v)

with the plasma side the total pressure of the two outermost half points
extrapolated to s = 1 (VMEC's 3/2, -1/2 rule) and P_vac swept over the segment
between the two answers: P_vac = P_mid + t dP with t in [-1, 1], where P_mid
and dP are the mean and half difference of the exact trigonometric
interpolants of NESTOR's and BIEST's pressures on the NESTOR grid. Each
interpolant is the unique one whose spectrum is the grid's own, with the
Nyquist terms carried as cosines. Every coefficient slot is widened by
2^-45, which holds the exact interpolant of the grid values however the
discrete Fourier transform rounded them; a coefficient below 2^-48 is
carried on the grid of 2^-100, inside that width.

`main --bt-tighten` fills in the cell bounds and `main --bt` establishes the
file: BoxCell.bt_surface then bounds |J| at every point of a field period of
the boundary, for every t in [-1, 1], by the largest cell bound.

  python gen/free_boundary.py cert WOUT VACNPZ OUT --nu 256 --nv 64
  main --bt-tighten OUT OUT_t && main --bt OUT_t
"""

import argparse
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from forced_sheet import dyadic53, state  # noqa: E402
from make_cert import (  # noqa: E402
    ANGLE_EXP,
    MU0,
    Wout,
    calibrate_pressure,
    half_point,
    pvalue_ref,
)

COEF_HALF_WIDTH_EXP = -45
COEF_FLOOR_EXP = -100
T_EXP = -30


def series_of_grid(P, nfp):
    """The exact trigonometric interpolant of grid values P[k, l] at
    v_k = 2 pi k / (nfp Nv) and u_l = 2 pi l / Nu, as {(m, n): [a, b]} with
    P(u, v) = sum a cos(m u - n v) + b sin(m u - n v), n a multiple of nfp.

    The interpolant is the discrete Fourier sum with every frequency in
    (-N/2, N/2) carried as an exponential and the Nyquist frequency of an even
    grid as a cosine, which is real for real data and equals P on the grid."""
    Nv, Nu = P.shape
    C = np.fft.fft2(P) / (Nv * Nu)
    out = {}

    def add(m, n, c):
        # c e^{i (m u - n v)}, real part only: the imaginary parts cancel
        if m < 0 or (m == 0 and n < 0):
            m, n, c = -m, -n, np.conj(c)
        a, b = out.setdefault((int(m), int(n)), [0.0, 0.0])
        out[(int(m), int(n))] = [a + c.real, b - c.imag]

    def freqs(k, N):
        if N % 2 == 0 and k == N // 2:
            return [(N // 2, 0.5), (-(N // 2), 0.5)]
        f = k if k <= N // 2 else k - N
        return [(f, 1.0)]

    for kk in range(Nv):
        for ll in range(Nu):
            c = C[kk, ll]
            for (lf, wl) in freqs(ll, Nu):
                for (kf, wk) in freqs(kk, Nv):
                    # e^{i (lf u + kf nfp v)} = e^{i (m u - n v)} with n = -kf nfp
                    add(lf, -kf * nfp, c * wl * wk)
    return out


def eval_series(sr, u, v):
    u = np.asarray(u, dtype=float)
    v = np.asarray(v, dtype=float)
    acc = np.zeros(np.broadcast(u, v).shape)
    for (m, n), (a, b) in sr.items():
        ang = m * u - n * v
        acc += a * np.cos(ang) + b * np.sin(ang)
    return acc


def tile_period(width, n, e):
    """Centres and half-width of n abutting cells from 0 whose span exceeds
    width by at least one unit per cell, so that the checker's enclosure of pi
    decides bt_period however width was rounded."""
    d = int(np.ceil(width / (2.0 * n) / 2.0**e)) + 1
    return [(2 * k + 1) * d for k in range(n)], d


def edge_pressure(w, j, u, v, phip):
    """The float reference of the plasma side: the total pressure of the two
    half points of node j, mu0-scaled, extrapolated linearly to s = 1."""
    qm = half_point(w, j - 1, j, j, u, v, phip)
    qp = half_point(w, j, j + 1, j + 1, u, v, phip)
    sm, sp = w.s_half[j], w.s_half[j + 1]
    tm = 0.5 * qm["B2"] + MU0 * pvalue_ref(w.profile, w.am, sm)
    tp = 0.5 * qp["B2"] + MU0 * pvalue_ref(w.profile, w.am, sp)
    return tp + (1.0 - sp) * (tp - tm) / (sp - sm)


def load(wout_path, vac_path):
    w = Wout(wout_path)
    calibrate_pressure(w)
    vac = np.load(vac_path)
    return w, vac


def vacuum_block(sr_mid, sr_dif, modes):
    """The slots of the vacuum block: the mean series' cosine and sine
    coefficients mode by mode, then the half difference's, then t."""
    out = []
    for sr in (sr_mid, sr_dif):
        for mn in modes:
            for x in sr.get(mn, [0.0, 0.0]):
                M, E = dyadic53(x, COEF_FLOOR_EXP)
                if E < COEF_FLOOR_EXP:
                    # below the floor the coefficient is rounded onto 2^-100,
                    # an error the half-width covers many times over
                    M, E = int(round(x * 2.0**-COEF_FLOOR_EXP)), COEF_FLOOR_EXP
                d = 2 ** max(0, COEF_HALF_WIDTH_EXP - E)
                out.append((M, E, d))
    out.append((0, T_EXP, 2 ** (-T_EXP)))
    return out


def cmd_probe(a):
    """Float statistics of the jump for choosing the cells."""
    w, vac = load(a.wout, a.vac)
    nfp = int(round(2 * np.pi / (vac["phi"][1] - vac["phi"][0]) / len(vac["phi"])))
    j = w.ns - 2
    phip = float(w.phips[1])
    sN = series_of_grid(vac["pn"], nfp)
    sB = series_of_grid(vac["pb"], nfp)
    U, V = np.meshgrid(vac["theta"], vac["phi"])
    print(f"nfp {nfp}, node {j} (s = {w.s_full[j]:.6f}), {len(sN)} vacuum modes; "
          f"grid reproduction {np.abs(eval_series(sN, U, V) - vac['pn']).max():.1e}, "
          f"{np.abs(eval_series(sB, U, V) - vac['pb']).max():.1e}")
    te_grid = np.array([[edge_pressure(w, j, u, v, phip) for u in vac["theta"]]
                        for v in vac["phi"]])
    print(f"plasma side against VMEC++'s bsqmhdf on the grid: "
          f"{np.abs(te_grid - vac['tp']).max():.3e}")
    nu, nv = a.nu, a.nv
    us = 2 * np.pi * (np.arange(nu) + 0.5) / nu
    vs = 2 * np.pi / nfp * (np.arange(nv) + 0.5) / nv
    UU, VV = np.meshgrid(us, vs)
    te = np.array([[edge_pressure(w, j, u, v, phip) for u in us] for v in vs])
    for name, sr in (("NESTOR", sN), ("BIEST", sB)):
        J = te - eval_series(sr, UU, VV)
        Ju = np.gradient(J, us, axis=1)
        Jv = np.gradient(J, vs, axis=0)
        Juu = np.gradient(Ju, us, axis=1)
        Jvv = np.gradient(Jv, vs, axis=0)
        k = np.unravel_index(np.abs(J).argmax(), J.shape)
        print(f"{name}: max|J| {np.abs(J).max():.4e} at u {us[k[1]]:.3f} v {vs[k[0]]:.4f}; "
              f"max|J_u| {np.abs(Ju).max():.2e} |J_v| {np.abs(Jv).max():.2e} "
              f"|J_uu| {np.abs(Juu).max():.2e} |J_vv| {np.abs(Jvv).max():.2e}")


def jump_state(a, t_only=None):
    """The wout, the vacuum series and the header lines every certificate of
    the jump shares; with t_only the sweep slot is pinned to that value."""
    w, vac = load(a.wout, a.vac)
    nfp = int(round(2 * np.pi / (vac["phi"][1] - vac["phi"][0]) / len(vac["phi"])))
    j = w.ns - 2
    phip = float(w.phips[1])
    sN = series_of_grid(vac["pn"], nfp)
    sB = series_of_grid(vac["pb"], nfp)
    modes = sorted(set(sN) | set(sB))
    mid = {mn: [(sN.get(mn, [0, 0])[i] + sB.get(mn, [0, 0])[i]) / 2 for i in (0, 1)]
           for mn in modes}
    dif = {mn: [(sN.get(mn, [0, 0])[i] - sB.get(mn, [0, 0])[i]) / 2 for i in (0, 1)]
           for mn in modes}
    U, V = np.meshgrid(vac["theta"], vac["phi"])
    for t, P, name in ((1.0, vac["pn"], "NESTOR"), (-1.0, vac["pb"], "BIEST")):
        err = np.abs(eval_series(mid, U, V) + t * eval_series(dif, U, V) - P).max()
        print(f"t = {t:+.0f} reproduces {name}'s grid pressure to {err:.1e}")
    # --widen k sweeps k times the half difference, so t in [-1, 1] covers every
    # pressure within k times the two answers' disagreement of their mean
    k = getattr(a, "widen", 1.0)
    dif = {mn: [k * x for x in c] for mn, c in dif.items()}
    K = len(w.xm)
    st = state(w, j, phip, 0.0) + vacuum_block(mid, dif, modes)
    if t_only is not None:
        st[-1] = (int(t_only * 2 ** (-T_EXP)), T_EXP, 0)
    assert len(st) == 32 + 8 * K + 4 * len(modes) + 1
    head = ["PREC 53", "LASYM 0", f"PROFILE {w.profile}",
            f"OUTPUT jump {len(modes)} " + " ".join(f"{m} {n}" for m, n in modes),
            f"MODES {K}"]
    head += [f"{m} {n}" for m, n in zip(w.xm, w.xn, strict=True)]
    head += [f"NSLOTS {len(st)}", "STATE"] + [f"{m} {e} {d}" for m, e, d in st]
    head += ["SLOTS 1 2", f"COMP {getattr(a, 'comp', 0)}"]
    return w, vac, nfp, j, phip, sN, sB, modes, st, head


def cmd_grid(a):
    """Point certificates of the jump at every point of the NESTOR grid: a
    ceiling at each, over both vacuum answers (t in [-1, 1]), and, with t
    pinned to 1, a floor on NESTOR's jump where it is largest."""
    w, vac, nfp, j, phip, sN, sB, modes, st, head = jump_state(a)
    th, ph = vac["theta"], vac["phi"]
    pts = [(round(u / 2.0**ANGLE_EXP), round(v / 2.0**ANGLE_EXP)) for v in ph for u in th]
    L = ["STELLAROCQ-BPCERT"] + head + [f"POINTS {len(pts)}"]
    L += [f"{mu} {mv} 1 0 0" for mu, mv in pts]
    pathlib.Path(a.out + "_ceil.txt").write_text("\n".join(L) + "\n")
    te = np.array([[edge_pressure(w, j, u, v, phip) for u in th] for v in ph])
    jn = te - vac["pn"]
    k = np.unravel_index(np.abs(jn).argmax(), jn.shape)
    mu, mv = round(th[k[1]] / 2.0**ANGLE_EXP), round(ph[k[0]] / 2.0**ANGLE_EXP)
    *_, head1 = jump_state(a, t_only=1.0)
    L = ["STELLAROCQ-BPCERT"] + head1 + ["POINTS 1", f"{mu} {mv} 1 0 1"]
    pathlib.Path(a.out + "_floor.txt").write_text("\n".join(L) + "\n")
    print(f"wrote {a.out}_ceil.txt ({len(pts)} points) and {a.out}_floor.txt; "
          f"float max |J| NESTOR {np.abs(jn).max():.6e} at u {th[k[1]]:.4f} v {ph[k[0]]:.4f}, "
          f"BIEST {np.abs(te - vac['pb']).max():.6e}")


def cmd_cert(a):
    w, vac, nfp, j, phip, sN, sB, modes, st, head = jump_state(a)
    K = len(w.xm)
    ums, du = tile_period(2.0 * np.pi, a.nu, ANGLE_EXP)
    vms, dv = tile_period(2.0 * np.pi / nfp, a.nv, ANGLE_EXP)
    L = ["STELLAROCQ-BTCERT"] + head
    P_ = L.append
    P_(f"HALF {du} {dv}")
    P_(f"GRID 0 0 {a.nu} {a.nv} {nfp}")
    P_(f"CELLS {a.nu * a.nv}")
    for mv in vms:
        for mu in ums:
            P_(f"{mu} {mv} 1 0 1 0 1 0 1 0 1 0")
    pathlib.Path(a.out).write_text("\n".join(L) + "\n")
    print(f"wrote {a.out}: node {j} of ns = {w.ns}, K = {K}, {len(modes)} vacuum modes, "
          f"{len(st)} slots, {a.nu} by {a.nv} cells")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, fn in (("probe", cmd_probe), ("cert", cmd_cert), ("grid", cmd_grid)):
        s = sub.add_parser(name)
        s.add_argument("wout")
        s.add_argument("vac", help="npz with pn, pb, tp, theta, phi on the NESTOR grid")
        if name == "grid":
            s.add_argument("out", help="prefix of the two certificates")
        if name == "cert":
            s.add_argument("out")
            s.add_argument("--comp", type=int, default=0, choices=[0, 1, 2],
                           help="0 the jump, 1 the plasma-side edge pressure, "
                           "2 the vacuum pressure")
        s.add_argument("--widen", type=float, default=1.0,
                       help="sweep this many times the half difference of the answers")
        s.add_argument("--nu", type=int, default=256)
        s.add_argument("--nv", type=int, default=64)
        s.set_defaults(fn=fn)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
