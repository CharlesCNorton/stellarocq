"""VMEC++ against Landreman's exact equilibria, over whole surfaces.

Landreman (arXiv:2609.26742) gives two families of exact ideal-MHD equilibria
whose field B* and flux label psi* are elementary functions of the Cartesian
position: the family with iota = 2, whose field theories/Landreman.v proves an
equilibrium, and the sheared family. This file writes the certificates of
Physics.RExactField and Physics.RExactFlux for a wout of such a member, as
coverings of a field period of a surface by Taylor cells (STELLAROCQ-BTCERT,
BoxCell.bt_surface):

  field  at the half point outside node j, each cylindrical component of
         B - B*(X), B the field the half-grid rule reconstructs from the wout
         and X its position, so a verdict bounds that component at every
         point of the half-grid surface;
  flux   on the node surface, psi*(X) less a value c, so a verdict puts the
         whole surface between the level sets psi* = c - d and c + d.

The member's parameters go in the four slots after the state: a, b for the
family with iota = 2 (a = sqrt(1 + eps), b = sqrt(1 - eps)) and eps, S,
lambda for the sheared one, then c. They are the binary64 values of the
member, each an exact dyadic in the file.

  python gen/landreman.py survey WOUT iota2 --eps 0.25
  python gen/landreman.py run WOUT sheared --eps 0.6 --S 2.2 --lam 2.97 \\
         --main PATH --out DIR [--nu 128 --nv 64] [--nodes 1,5,9]

  python gen/landreman.py points WOUT sheared --eps 0.6 --S 2.2 --lam 2.97 \\
         --main PATH --out DIR [--nu 64 --nv 32] [--nodes 1,5,9]

  python gen/landreman.py floor WOUT iota2 --eps 0.25 --main PATH --out DIR \\
         [--nu 192 --nv 96] [--nodes J]

`survey` prints the floating-point largest |B - B*| and the spread of psi* on
every surface, from the same formulas; `run` writes, tightens and checks the
certificates of every surface and component, and writes DIR/summary.json;
`points` certifies each component at the points of a grid of a field period
(STELLAROCQ-BPCERT, BoxCell.check_bpcert_correct) on every surface and writes
DIR/points.json; `floor` bounds |B - B*| from below on the middle half-grid
surface, or outside each node of --nodes, by a floor on the magnitude of the
component at the grid point where it is largest, and writes DIR/floor.json.

  python gen/landreman.py spectrum WOUT iota2 --eps 0.25 --iota -2

`spectrum` splits B - B* on the middle and outermost half-grid surfaces into
Fourier harmonics in floating point, and prints the largest and the share of
the spectral power in the harmonics resonant with --iota (VMEC's sign), which
for the member with iota = 2 is where VMEC++'s error lies.
"""

import argparse
import json
import math
import os
import pathlib
import re
import subprocess
import sys
import time

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from forced_sheet import dyadic53  # noqa: E402
from free_boundary import tile_period  # noqa: E402
from make_cert import ANGLE_EXP, Wout, calibrate_pressure  # noqa: E402

FAMILY = {"iota2": 0, "sheared": 1}


def point(x):
    M, E = dyadic53(x)
    return (M, E, 0)


def nfp_of(w):
    """The field periods, the gcd of the toroidal mode numbers."""
    xn = np.abs(np.asarray(w.xn))
    return int(np.gcd.reduce(xn[xn != 0])) if np.any(xn != 0) else 1


def params(fam, a):
    if fam == "iota2":
        return [math.sqrt(1.0 + a.eps), math.sqrt(1.0 - a.eps), 0.0]
    return [a.eps, a.S, a.lam]


def exact(fam, p, x, y, z):
    """B* and psi* at (x, y, z), as Physics.exact_b builds them."""
    if fam == "iota2":
        a, b = p[0], p[1]
        s = x * x / (a * a) + y * y / (b * b)
        F = np.sqrt(1.0 - (1.0 - s) ** 2 - 4.0 * z * z)
        bx = (2.0 * z * x - (a / b) * F * y) / s
        by = (2.0 * z * y + (b / a) * F * x) / s
        bz = 1.0 - s
        eps = (a * a - b * b) / 2.0
        psi = (x * x + y * y + 4.0 * z * z + bx * bx + by * by + bz * bz - 2.0 + eps * eps) / 4.0
        return bx, by, bz, psi
    eps, S, lam = p
    w = x + 1j * y
    wb = x - 1j * y
    k = wb * np.sqrt(1.0 + eps / wb**2)
    xi = w * k + np.pi / 2.0 - S
    e = np.exp(-1j * lam * z)
    bxy = e * 1j * np.sin(xi) / (2.0 * k)
    bz = np.real(e * np.cos(xi)) / lam
    psi = (np.sin(lam * z) ** 2 + (lam * bz) ** 2) / 2.0
    return np.real(bxy), np.imag(bxy), bz, psi


def half_geometry(w, j, u, v):
    """R, Z and their derivatives at the half point between nodes j and j + 1
    by the half-grid rule of Physics.halfcoef_b, and lambda_u, lambda_v there."""
    xm, xn = np.asarray(w.xm, float), np.asarray(w.xn, float)
    sa, sb, sh = w.s_full[j], w.s_full[j + 1], w.s_half[j + 1]
    odd = (xm % 2) == 1

    def half(c):
        ca, cb = np.asarray(c[j], float), np.asarray(c[j + 1], float)
        qa = ca / np.sqrt(sa) if sa > 0 else 0.0 * ca
        qb = cb / np.sqrt(sb)
        c_odd = np.sqrt(sh) * 0.5 * (qa + qb)
        cs_odd = np.sqrt(sh) * (qb - qa) / (sb - sa) + c_odd / (2.0 * sh)
        c_even = 0.5 * (ca + cb)
        cs_even = (cb - ca) / (sb - sa)
        return np.where(odd, c_odd, c_even), np.where(odd, cs_odd, cs_even)

    rc, rcs = half(w.rmnc)
    zc, zcs = half(w.zmns)
    lc = np.asarray(w.lmns[j + 1], float)
    arg = np.multiply.outer(u, xm) - np.multiply.outer(v, xn)
    C, Sn = np.cos(arg), np.sin(arg)
    R, Rs = C @ rc, C @ rcs
    Ru, Rv = -Sn @ (xm * rc), Sn @ (xn * rc)
    Z, Zs = Sn @ zc, Sn @ zcs
    Zu, Zv = C @ (xm * zc), -C @ (xn * zc)
    Lu, Lv = C @ (xm * lc), -C @ (xn * lc)
    return R, Z, Ru, Rv, Rs, Zu, Zv, Zs, Lu, Lv


def field_ref(w, j, u, v, fam, p, phip):
    """B - B*(X) at the half point outside node j, cylindrical components."""
    R, Z, Ru, Rv, Rs, Zu, Zv, Zs, Lu, Lv = half_geometry(w, j, u, v)
    sg = R * (Ru * Zs - Rs * Zu)
    iota = float(w.iotas[j + 1])
    Bu = phip * (iota - Lv) / sg
    Bv = phip * (1.0 + Lu) / sg
    BR, BP, BZ = Bu * Ru + Bv * Rv, Bv * R, Bu * Zu + Bv * Zv
    cv, sv = np.cos(v), np.sin(v)
    bx, by, bz, _ = exact(fam, p, R * cv, R * sv, Z)
    return BR - (bx * cv + by * sv), BP - (by * cv - bx * sv), BZ - bz, np.sqrt(bx**2 + by**2 + bz**2)


def flux_ref(w, j, u, v, fam, p):
    """psi*(X) on the node surface j."""
    xm, xn = np.asarray(w.xm, float), np.asarray(w.xn, float)
    arg = np.multiply.outer(u, xm) - np.multiply.outer(v, xn)
    R = np.cos(arg) @ np.asarray(w.rmnc[j], float)
    Z = np.sin(arg) @ np.asarray(w.zmns[j], float)
    return exact(fam, p, R * np.cos(v), R * np.sin(v), Z)[3]


def grid(nfp, nu=192, nv=96):
    u = 2 * np.pi * (np.arange(nu) + 0.5) / nu
    v = 2 * np.pi / nfp * (np.arange(nv) + 0.5) / nv
    U, V = np.meshgrid(u, v)
    return U.ravel(), V.ravel()


def state(w, j, phip, rows):
    """The environment of node j in Physics.v's order, the R, Z and lambda
    rows taken from `rows` (inner, node, outer) so that the boundary node can
    repeat itself as the row outside it, which RExactFlux never reads."""
    ja, jj, jb = rows
    st = [point(w.s_full[jj]), (0, ANGLE_EXP, 0), (0, ANGLE_EXP, 0), point(phip)]
    st += [point(w.s_full[r]) for r in rows]
    st += [point(w.s_half[r]) for r in (jj, jb)]
    st += [point(w.iotas[r]) for r in (jj, jb)]
    st += [point(w.am[i] if i < len(w.am) else 0.0) for i in range(21)]
    for block in (w.rmnc, w.zmns):
        for r in rows:
            st += [point(x) for x in block[r]]
    for r in (jj, jb):
        st += [point(x) for x in w.lmns[r]]
    return st


def write_cert(w, j, kind, fam, p, c, comp, nu, nv, out):
    K = len(w.xm)
    phip = float(w.phips[1])
    last = w.ns - 1
    rows = (j - 1, j, j + 1) if j < last else (j - 1, j, j)
    st = state(w, j, phip, rows) + [point(x) for x in (*p, c)]
    nfp = nfp_of(w)
    ums, du = tile_period(2.0 * np.pi, nu, ANGLE_EXP)
    vms, dv = tile_period(2.0 * np.pi / nfp, nv, ANGLE_EXP)
    L = ["STELLAROCQ-BTCERT", "PREC 53", "LASYM 0", f"PROFILE {w.profile}",
         f"OUTPUT exact-{kind} {FAMILY[fam]}", f"MODES {K}"]
    L += [f"{m} {n}" for m, n in zip(w.xm, w.xn, strict=True)]
    L += [f"NSLOTS {len(st)}", "STATE"] + [f"{m} {e} {d}" for m, e, d in st]
    L += ["SLOTS 1 2", f"COMP {comp}", f"HALF {du} {dv}",
          f"GRID 0 0 {nu} {nv} {nfp}", f"CELLS {nu * nv}"]
    L += [f"{mu} {mv} 1 0 1 0 1 0 1 0 1 0" for mv in vms for mu in ums]
    pathlib.Path(out).write_text("\n".join(L) + "\n")


def write_points(w, j, kind, fam, p, c, comp, nu, nv, out, pts=None, mode=0):
    """The point certificate of one component on a grid of a field period of the
    surface: nu by nv angles, u = 2 pi (l + 1/2) / nu and v = (2 pi / nfp)
    (k + 1/2) / nv, each rounded to the angle slots' dyadic grid, with a
    ceiling on |component| at each (mode 0) that `main --bp-tighten` fills in.
    Given pts, a list of angle mantissa pairs, the certificate names those
    points instead, each with the claim of `mode`, 1 for a floor on
    |component|."""
    K = len(w.xm)
    phip = float(w.phips[1])
    last = w.ns - 1
    rows = (j - 1, j, j + 1) if j < last else (j - 1, j, j)
    st = state(w, j, phip, rows) + [point(x) for x in (*p, c)]
    nfp = nfp_of(w)
    L = ["STELLAROCQ-BPCERT", "PREC 53", "LASYM 0", f"PROFILE {w.profile}",
         f"OUTPUT exact-{kind} {FAMILY[fam]}", f"MODES {K}"]
    L += [f"{m} {n}" for m, n in zip(w.xm, w.xn, strict=True)]
    L += [f"NSLOTS {len(st)}", "STATE"] + [f"{m} {e} {d}" for m, e, d in st]
    L += ["SLOTS 1 2", f"COMP {comp}"]
    if pts is None:
        us = 2.0 * np.pi * (np.arange(nu) + 0.5) / nu
        vs = 2.0 * np.pi / nfp * (np.arange(nv) + 0.5) / nv
        pts = [(round(u / 2.0**ANGLE_EXP), round(v / 2.0**ANGLE_EXP)) for v in vs for u in us]
    L += [f"POINTS {len(pts)}"] + [f"{mu} {mv} 1 0 {mode}" for mu, mv in pts]
    pathlib.Path(out).write_text("\n".join(L) + "\n")


def cmd_points(a):
    """Every half-grid surface's field and every node surface's psi*, certified
    at the points of a grid: the largest ceiling over the grid for each."""
    w = Wout(a.wout)
    calibrate_pressure(w)
    p = params(a.family, a)
    phip = float(w.phips[1])
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    U, V = grid(nfp_of(w))
    nodes = ([int(x) for x in a.nodes.split(",")] if a.nodes
             else list(range(1, w.ns)))
    rows = []
    for j in nodes:
        row = {"node": j, "s": float(w.s_full[j])}
        ps = flux_ref(w, j, U, V, a.family, p)
        c = 0.5 * (float(ps.min()) + float(ps.max()))
        row["c"], row["float_spread"] = c, float(ps.max() - ps.min())
        jobs = [("flux", 0)]
        if j < w.ns - 1:
            row["s_half"] = float(w.s_half[j + 1])
            dR, dP, dZ, B = field_ref(w, j, U, V, a.family, p, phip)
            row["float_dB"] = float(np.sqrt(dR**2 + dP**2 + dZ**2).max())
            row["B_min"] = float(B.min())
            jobs += [("field", k) for k in (0, 1, 2)]
        for kind, comp in jobs:
            src = out / f"p{kind}_{j}_{comp}.txt"
            tgt = out / f"p{kind}_{j}_{comp}_t.txt"
            write_points(w, j, kind, a.family, p, c, comp, a.nu, a.nv, src)
            run_main(a.main, "--bp-tighten", str(src), str(tgt))
            rc, o = run_main(a.main, "--bp", str(tgt))
            m = re.search(r"largest ceiling: ([0-9.eE+-]+)", o)
            v = re.search(r"verdict: (\w+)", o)
            row[f"{kind}{comp}"] = {"ceiling": float(m.group(1)) if m else None,
                                    "verdict": v.group(1) if v else "NONE"}
            src.unlink(missing_ok=True)
            if not a.keep:
                tgt.unlink(missing_ok=True)
        print(json.dumps(row), flush=True)
        rows.append(row)
    (out / "points.json").write_text(json.dumps(
        {"wout": str(a.wout), "family": a.family, "params": p, "nu": a.nu, "nv": a.nv,
         "rows": rows}, indent=1))


def cmd_floor(a):
    """|B - B*| bounded below on half-grid surfaces: at the point of a grid of
    a field period and the component where the difference is largest in
    floating point, a floor on the component's magnitude (mode 1), certified
    at that point."""
    w = Wout(a.wout)
    calibrate_pressure(w)
    p = params(a.family, a)
    phip = float(w.phips[1])
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    U, V = grid(nfp_of(w), a.nu, a.nv)
    MU, MV = np.round(U / 2.0**ANGLE_EXP), np.round(V / 2.0**ANGLE_EXP)
    nodes = [int(x) for x in a.nodes.split(",")] if a.nodes else [(w.ns - 1) // 2]
    rows = []
    for j in nodes:
        # the largest component at the points the certificate names
        dB = np.abs(np.stack(field_ref(w, j, MU * 2.0**ANGLE_EXP, MV * 2.0**ANGLE_EXP,
                                       a.family, p, phip)[:3]))
        comp, i = (int(x) for x in np.unravel_index(np.argmax(dB), dB.shape))
        src = out / f"pfloor_{j}_{comp}.txt"
        tgt = out / f"pfloor_{j}_{comp}_t.txt"
        write_points(w, j, "field", a.family, p, 0.0, comp, 0, 0, src,
                     pts=[(int(MU[i]), int(MV[i]))], mode=1)
        run_main(a.main, "--bp-tighten", str(src), str(tgt))
        rc, o = run_main(a.main, "--bp", str(tgt))
        m = re.search(r"\|component\| >= ([0-9.eE+-]+)", o)
        v = re.search(r"verdict: (\w+)", o)
        row = {"node": j, "s_half": float(w.s_half[j + 1]), "comp": comp,
               "mantissas": [int(MU[i]), int(MV[i])], "float": float(dB[comp, i]),
               "floor": float(m.group(1)) if m else None,
               "verdict": v.group(1) if v else "NONE"}
        src.unlink(missing_ok=True)
        print(json.dumps(row), flush=True)
        rows.append(row)
    (out / "floor.json").write_text(json.dumps(
        {"wout": str(a.wout), "family": a.family, "params": p, "nu": a.nu, "nv": a.nv,
         "rows": rows}, indent=1))


def run_main(main, *args):
    p = subprocess.run([main, *args], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       text=True, env=dict(os.environ))
    return p.returncode, p.stdout


def cmd_survey(a):
    w = Wout(a.wout)
    calibrate_pressure(w)
    p = params(a.family, a)
    phip = float(w.phips[1])
    U, V = grid(nfp_of(w))
    print(f"{a.family}: ns {w.ns}, nfp {nfp_of(w)}, K {len(w.xm)}, phip {phip:+.6e}")
    for j in range(1, w.ns - 1):
        dR, dP, dZ, B = field_ref(w, j, U, V, a.family, p, phip)
        ps = flux_ref(w, j, U, V, a.family, p)
        print(f"  half point {w.s_half[j + 1]:.5f}: |dB| max {np.sqrt(dR**2 + dP**2 + dZ**2).max():.3e} "
              f"(|B*| {B.min():.3f} to {B.max():.3f}); node {w.s_full[j]:.5f}: psi* "
              f"{ps.min():.9e} to {ps.max():.9e}")


def cmd_run(a):
    w = Wout(a.wout)
    calibrate_pressure(w)
    p = params(a.family, a)
    phip = float(w.phips[1])
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    U, V = grid(nfp_of(w))
    nodes = ([int(x) for x in a.nodes.split(",")] if a.nodes
             else list(range(1, w.ns - 1)))
    rows = []
    for j in nodes:
        row = {"node": j, "s": float(w.s_full[j]), "s_half": float(w.s_half[j + 1])}
        dR, dP, dZ, B = field_ref(w, j, U, V, a.family, p, phip)
        row["float_dB"] = float(np.sqrt(dR**2 + dP**2 + dZ**2).max())
        row["B_min"] = float(B.min())
        ps = flux_ref(w, j, U, V, a.family, p)
        c = 0.5 * (float(ps.min()) + float(ps.max()))
        row["c"] = c
        row["float_spread"] = float(ps.max() - ps.min())
        for kind, comps in (("field", (0, 1, 2)), ("flux", (0,))):
            for comp in comps:
                t0 = time.time()
                src = out / f"{kind}_{j}_{comp}.txt"
                tgt = out / f"{kind}_{j}_{comp}_t.txt"
                write_cert(w, j, kind, a.family, p, c, comp, a.nu, a.nv, src)
                rc, o1 = run_main(a.main, "--bt-tighten", str(src), str(tgt))
                rc, o2 = run_main(a.main, "--bt", str(tgt))
                m = re.search(r"bound over the surface: ([0-9.eE+-]+)", o2)
                v = re.search(r"verdict: (\w+)", o2)
                row[f"{kind}{comp}"] = {
                    "bound": float(m.group(1)) if m else None,
                    "verdict": v.group(1) if v else "NONE",
                    "seconds": round(time.time() - t0, 2)}
                if not a.keep:
                    src.unlink(missing_ok=True)
        print(json.dumps(row), flush=True)
        rows.append(row)
    (out / "summary.json").write_text(json.dumps(
        {"wout": str(a.wout), "family": a.family, "params": p, "nu": a.nu, "nv": a.nv,
         "rows": rows}, indent=1))


def cmd_spectrum(a):
    """The Fourier harmonics of B - B* on half-grid surfaces, in floating
    point: the largest, and the share of the spectral power in the harmonics
    resonant with a transform iota, m iota = n nfp in VMEC's convention."""
    w = Wout(a.wout)
    calibrate_pressure(w)
    p = params(a.family, a)
    phip = float(w.phips[1])
    nfp = nfp_of(w)
    nu, nv = a.nu, a.nv
    u = 2 * np.pi * np.arange(nu) / nu
    v = 2 * np.pi / nfp * np.arange(nv) / nv
    U, V = np.meshgrid(u, v, indexing="ij")
    nodes = [int(x) for x in a.nodes.split(",")] if a.nodes else [(w.ns - 1) // 2, w.ns - 2]
    for j in nodes:
        comps = field_ref(w, j, U.ravel(), V.ravel(), a.family, p, phip)[:3]
        spec, tot, res = {}, 0.0, 0.0
        for comp in comps:
            F = np.fft.fft2(comp.reshape(nu, nv)) / (nu * nv)
            for i in range(nu):
                for k in range(nv):
                    m = i if i <= nu // 2 else i - nu
                    n = -(k if k <= nv // 2 else k - nv)
                    if m < 0 or (m == 0 and n < 0):
                        m, n = -m, -n
                    power = abs(F[i, k]) ** 2
                    spec[(m, n)] = spec.get((m, n), 0.0) + power
                    tot += power
                    if m != 0 and abs(m * a.iota - n * nfp) < 1e-9:
                        res += power
        top = sorted(spec.items(), key=lambda kv: -kv[1])[:5]
        err = float(np.sqrt(sum(c**2 for c in comps)).max())
        print(f"{pathlib.Path(a.wout).name} s {w.s_half[j + 1]:.3f}: max |B - B*| {err:.2e}, "
              f"resonant share {res / tot:.3f}; largest (m,n): "
              + ", ".join(f"({m},{n}) {np.sqrt(e):.1e}" for (m, n), e in top), flush=True)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("spectrum")
    s.add_argument("wout")
    s.add_argument("family", choices=list(FAMILY))
    s.add_argument("--eps", type=float, required=True)
    s.add_argument("--S", type=float, default=0.0)
    s.add_argument("--lam", type=float, default=0.0)
    s.add_argument("--iota", type=float, default=-2.0,
                   help="the transform the resonance is taken against, VMEC's sign")
    s.add_argument("--nu", type=int, default=64)
    s.add_argument("--nv", type=int, default=64)
    s.add_argument("--nodes", default="")
    s.set_defaults(fn=cmd_spectrum)
    for name, fn in (("survey", cmd_survey), ("run", cmd_run), ("points", cmd_points),
                     ("floor", cmd_floor)):
        s = sub.add_parser(name)
        s.add_argument("wout")
        s.add_argument("family", choices=list(FAMILY))
        s.add_argument("--eps", type=float, required=True)
        s.add_argument("--S", type=float, default=0.0)
        s.add_argument("--lam", type=float, default=0.0)
        if name in ("run", "points", "floor"):
            s.add_argument("--main", required=True)
            s.add_argument("--out", required=True)
            s.add_argument("--nu", type=int, default=192 if name == "floor" else 128)
            s.add_argument("--nv", type=int, default=96 if name == "floor" else 64)
            s.add_argument("--nodes", default="")
            s.add_argument("--keep", action="store_true")
        s.set_defaults(fn=fn)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
