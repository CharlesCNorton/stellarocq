"""The forced current sheet of a rippled circular tokamak, over a box of states.

A tokamak whose boundary carries a (1,1) ripple drives, through toroidal
coupling, a (2,1) sideband at the surface where iota = 1/2. A field with nested
surfaces cannot balance that resonant force there: the ideal response is a
current sheet, which no smooth nested field represents. The discrete solver
still converges, because its grid smooths the sheet, and what shows the
obstruction is the continuum residual of its reconstruction, whose resonant
harmonic stays put as the grid is refined while every other harmonic falls
fourfold per doubling (gen/resonance.py tabulates this).

This file turns that observation into a certificate about every nested field
near the solution rather than about the one the solver returned. It writes a
STELLAROCQ-ICERT whose state box widens every R, Z and lambda coefficient of
the node's stencil by a relative half-width, and whose integrand is the radial
residual times cos(M u - N v) over the whole angular torus. `main --int`
establishes it with Integral.check_int_correct: for every state in the box the
integral exists and lies in the printed interval, so a printed floor excludes
force balance for all of them at once.

  python gen/forced_sheet.py solve --out DIR --ns 65,129,257
  python gen/forced_sheet.py icert DIR/wout_ns129.nc cert.txt --s 0.625 \\
         --harmonic 2,1 --rel 1e-9 --nu 64 --nv 32
  main --int-tighten cert.txt cert_t.txt && main --int cert_t.txt

The paper's certified (2,1) harmonic is Harmonic.dharm_correct for the equispaced
sum of r_s cos(2u - v) over a 64 by 32 grid, at the converged state with --rel 0
and for every state within a relative 1e-14 of it with --rel 1e-14, at each of
the three wouts of `solve`:

  python gen/forced_sheet.py hcert DIR/wout_ns65.nc hcert.txt --s 0.625 \\
         --harmonic 2,1 --rel 0 --nu 64 --nv 32 --output harmonic
  main --dharm hcert.txt
"""

import argparse
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from make_cert import ANGLE_EXP, Wout, calibrate_pressure, dyadic, tile  # noqa: E402


def dyadic53(x, e_floor=None):
    """x = M * 2^E exactly with |M| in [2^52, 2^53), so that a half-width in
    mantissa units is a relative width. Zero takes the exponent it is given."""
    x = float(x)
    if x == 0.0:
        return 0, (e_floor if e_floor is not None else 0)
    m, e = np.frexp(x)  # x = m 2^e, 0.5 <= |m| < 1
    E = int(e) - 53
    M = int(x * 2.0**-E) if abs(E) < 1000 else None
    # frexp is exact, and a double scaled by a power of two stays exact
    assert M is not None and M * 2.0**E == x
    return M, E


def box_block(values, rel):
    """Mantissa, exponent and half-width of every coefficient of a block, each
    widened by `rel` of its own size; an exact zero is widened by `rel` of the
    block's largest coefficient."""
    big = max((abs(float(v)) for v in values), default=0.0)
    e_big = dyadic53(big)[1] if big > 0.0 else 0
    out = []
    for v in values:
        M, E = dyadic53(v, e_big)
        if M == 0:
            d = int(round(rel * 2.0**52))
        else:
            d = int(round(rel * abs(M)))
        out.append((M, E, d))
    return out


def point(x):
    """A slot the box does not widen, at its exact value."""
    m, e = dyadic(x)
    return (m, e, 0)


def state(w, j, phip, rel):
    """The environment of node j in the order Physics.v reads it, each slot as
    (mantissa, exponent, half-width). The angle slots are overwritten by the
    cells and carry nothing."""
    K = len(w.xm)
    st = [point(w.s_full[j]), (0, ANGLE_EXP, 0), (0, ANGLE_EXP, 0), point(phip)]
    st += [point(x) for x in w.s_full[j - 1 : j + 2]]
    st += [point(x) for x in w.s_half[j : j + 2]]
    st += [point(x) for x in w.iotas[j : j + 2]]
    st += [point(w.am[i] if i < len(w.am) else 0.0) for i in range(21)]
    blocks = [w.rmnc[j - 1 : j + 2], w.zmns[j - 1 : j + 2], w.lmns[j : j + 2]]
    if w.lasym:
        blocks += [w.rmns[j - 1 : j + 2], w.zmnc[j - 1 : j + 2], w.lmnc[j : j + 2]]
    for rows in blocks:
        for r in rows:
            st += box_block(r, rel)
    assert len(st) == 32 + (16 if w.lasym else 8) * K
    return st


def write_icert(w, j, phip, out, harmonic, comp, rel, nu, nv, prec=53):
    K = len(w.xm)
    st = state(w, j, phip, rel)
    hm, hn = harmonic
    ums, du = tile(2.0 * np.pi, nu, ANGLE_EXP)
    vms, dv = tile(2.0 * np.pi, nv, ANGLE_EXP)
    L = []
    P = L.append
    P("STELLAROCQ-ICERT")
    P(f"PREC {prec}")
    P(f"LASYM {1 if w.lasym else 0}")
    P(f"PROFILE {w.profile}")
    P(f"OUTPUT harmonic {hm} {hn}")
    P(f"MODES {K}")
    for m, n in zip(w.xm, w.xn, strict=True):
        P(f"{m} {n}")
    P(f"NSLOTS {len(st)}")
    P("STATE")
    for m, e, d in st:
        P(f"{m} {e} {d}")
    P("SLOTS 1 2")
    P(f"COMP {comp}")
    P(f"U 0 {du} {nu}")
    P(f"V 0 {dv} {nv}")
    P("CELLS")
    for _ in range(nu * nv):
        P("1 0 1 0 1 0")
    pathlib.Path(out).write_text("\n".join(L) + "\n")
    span_u = 2 * nu * du * 2.0**ANGLE_EXP
    span_v = 2 * nv * dv * 2.0**ANGLE_EXP
    print(f"wrote {out}: node {j} (s = {w.s_full[j]:.6f}), K = {K}, "
          f"{len(st)} slots, {nu} by {nv} cells")
    print(f"the cells tile [0, {span_u!r}] x [0, {span_v!r}], "
          f"which exceeds the torus by {span_u - 2 * np.pi:.2e} and "
          f"{span_v - 2 * np.pi:.2e}")
    widened = sum(1 for _, _, d in st if d > 0)
    print(f"{widened} coefficient slots widened by {rel:g} of their size")


def write_hcert(w, j, phip, out, harmonic, comp, rel, nu, nv, prec=53,
                output="weighted"):
    """The certificate Harmonic.check_harm and check_dharm read: the residual
    (harmonic) or the weighted residual (weighted) against one kernel, over a
    box of states, at nu by nv equispaced angles."""
    K = len(w.xm)
    st = state(w, j, phip, rel)
    hm, hn = harmonic
    L = []
    P = L.append
    P("STELLAROCQ-HCERT")
    P(f"PREC {prec}")
    P(f"LASYM {1 if w.lasym else 0}")
    P(f"PROFILE {w.profile}")
    P(f"OUTPUT {output} {hm} {hn}")
    P(f"MODES {K}")
    for m, n in zip(w.xm, w.xn, strict=True):
        P(f"{m} {n}")
    P(f"NSLOTS {len(st)}")
    P("STATE")
    for m, e, d in st:
        P(f"{m} {e} {d}")
    P("SLOTS 1 2")
    P(f"COMP {comp}")
    P(f"GRID {nu} {nv}")
    pathlib.Path(out).write_text("\n".join(L) + "\n")
    widened = sum(1 for _, _, d in st if d > 0)
    print(f"wrote {out}: node {j} (s = {w.s_full[j]:.6f}), K = {K}, "
          f"{len(st)} slots, grid {nu} by {nv}, {widened} slots widened by {rel:g}")


def reference_weighted(w, j, phip, harmonic, nu=256, nv=128):
    """Float reference of the integral of (Gm Gp)^3 r_s cos(m u - n v) over the
    torus, by the same equispaced rule."""
    from make_cert import half_point

    hm, hn = harmonic
    acc = 0.0
    for a in range(nu):
        u = 2 * np.pi * a / nu
        for b in range(nv):
            v = 2 * np.pi * b / nv
            qm = half_point(w, j - 1, j, j, u, v, phip)
            qp = half_point(w, j, j + 1, j + 1, u, v, phip)
            from make_cert import residual_ref
            rs = residual_ref(w, j, u, v, phip)[0]
            acc += (qm["sqrtg"] * qp["sqrtg"]) ** 3 * rs * np.cos(hm * u - hn * v)
    return acc * (2 * np.pi / nu) * (2 * np.pi / nv)


def reference_harmonic(w, j, phip, harmonic, n=256):
    """A float reference for the integral, so a run can be read against it."""
    from make_cert import residual_ref

    hm, hn = harmonic
    us = 2 * np.pi * (np.arange(n) + 0.5) / n
    vs = 2 * np.pi * (np.arange(n // 2) + 0.5) / (n // 2)
    acc = np.zeros(3)
    for u in us:
        for v in vs:
            r = residual_ref(w, j, u, v, phip)[:3]
            acc += np.array(r) * np.cos(hm * u - hn * v)
    acc *= (2 * np.pi / n) * (2 * np.pi / (n // 2))
    return acc


def cmd_spectrum(a):
    """The discrete harmonics of r_s at the node of s, in floating point, by the
    equispaced sum the certified harmonic is: the rectangle rule for the
    integral of r_s cos(m u - n v) on nu by nv angles."""
    from make_cert import residual_ref

    w = Wout(a.wout)
    calibrate_pressure(w)
    phip = float(w.phips[1])
    node = round((w.ns - 1) * a.s)
    if abs(node - (w.ns - 1) * a.s) > 1e-9:
        raise SystemExit(f"s = {a.s} is not a node of ns = {w.ns}")
    us = 2 * np.pi * np.arange(a.nu) / a.nu
    vs = 2 * np.pi * np.arange(a.nv) / a.nv
    rs = np.array([[residual_ref(w, node, u, v, phip)[0] for v in vs] for u in us])
    weight = (2 * np.pi / a.nu) * (2 * np.pi / a.nv)
    print(f"{pathlib.Path(a.wout).name}: node {node} of ns = {w.ns}, grid {a.nu} by {a.nv}")
    for h in a.harmonics:
        hm, hn = (int(x) for x in h.split(","))
        kern = np.cos(hm * us[:, None] - hn * vs[None, :])
        print(f"({hm},{hn}) {weight * float((rs * kern).sum()):.6e}")


def cmd_solve(a):
    from resonance import solve

    import vmecpp

    base = a.base or str(pathlib.Path(vmecpp.__file__).parent / "cpp" / "vmecpp"
                         / "test_data" / "circular_tokamak.json")
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    m, n, amp = a.ripple.split(",")
    ripple = (int(m), int(n), float(amp))
    iota = [float(x) for x in a.iota.split(",")]
    for ns in (int(x) for x in a.ns.split(",")):
        solve(base, out, ripple, iota, a.pressure, a.ftol, ns, a.mpol, a.ntor)


def cmd_icert(a):
    w = Wout(a.wout)
    calibrate_pressure(w)
    phip = float(w.phips[1])
    node = round((w.ns - 1) * a.s)
    if abs(node - (w.ns - 1) * a.s) > 1e-9:
        raise SystemExit(f"s = {a.s} is not a node of ns = {w.ns}")
    harmonic = tuple(int(x) for x in a.harmonic.split(","))
    comp = {"r_s": 0, "r_u": 1, "r_v": 2}[a.component]
    write_icert(w, node, phip, a.out, harmonic, comp, a.rel, a.nu, a.nv)
    if a.reference:
        acc = reference_harmonic(w, node, phip, harmonic)
        print(f"float reference of the harmonic: r_s {acc[0]:.6e} "
              f"r_u {acc[1]:.6e} r_v {acc[2]:.6e}")


def cmd_hcert(a):
    w = Wout(a.wout)
    calibrate_pressure(w)
    phip = float(w.phips[1])
    node = round((w.ns - 1) * a.s)
    if abs(node - (w.ns - 1) * a.s) > 1e-9:
        raise SystemExit(f"s = {a.s} is not a node of ns = {w.ns}")
    harmonic = tuple(int(x) for x in a.harmonic.split(","))
    comp = {"cos": 0, "sin": 1, "plain": 2}[a.kernel]
    write_hcert(w, node, phip, a.out, harmonic, comp, a.rel, a.nu, a.nv,
                output=a.output)
    if a.reference:
        ref = reference_weighted(w, node, phip, harmonic, a.nu, a.nv)
        print(f"float reference of the weighted harmonic: {ref:.9e}")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("solve", help="run VMEC++ on the rippled tokamak")
    s.add_argument("--out", required=True)
    s.add_argument("--ripple", default="1,1,0.03")
    s.add_argument("--iota", default="0.9,-0.64")
    s.add_argument("--pressure", type=float, default=0.0)
    s.add_argument("--ftol", type=float, default=1.0e-15)
    s.add_argument("--mpol", type=int, default=8)
    s.add_argument("--ntor", type=int, default=4)
    s.add_argument("--ns", default="65,129,257")
    s.add_argument("--base", default=None)
    s.set_defaults(fn=cmd_solve)
    c = sub.add_parser("icert", help="write the integral certificate of a node")
    c.add_argument("wout")
    c.add_argument("out")
    c.add_argument("--s", type=float, default=0.625)
    c.add_argument("--harmonic", default="2,1")
    c.add_argument("--component", default="r_s", choices=["r_s", "r_u", "r_v"])
    c.add_argument("--rel", type=float, default=1e-9,
                   help="half-width of every R, Z and lambda coefficient, as a "
                   "fraction of its size")
    c.add_argument("--nu", type=int, default=64)
    c.add_argument("--nv", type=int, default=32)
    c.add_argument("--reference", action="store_true")
    c.set_defaults(fn=cmd_icert)
    h = sub.add_parser("hcert", help="write the exact harmonic certificate of a node")
    h.add_argument("wout")
    h.add_argument("out")
    h.add_argument("--s", type=float, default=0.625)
    h.add_argument("--harmonic", default="2,1")
    h.add_argument("--kernel", default="cos", choices=["cos", "sin", "plain"])
    h.add_argument("--rel", type=float, default=0.0,
                   help="half-width of every R, Z and lambda coefficient, as a "
                   "fraction of its size")
    h.add_argument("--nu", type=int, default=160)
    h.add_argument("--nv", type=int, default=96)
    h.add_argument("--reference", action="store_true")
    h.add_argument("--output", default="weighted", choices=["weighted", "harmonic"],
                   help="harmonic: the residual r_s against the kernel, whose "
                   "equispaced sum main --dharm certifies; weighted: the "
                   "residual cleared of the Jacobian, whose integral over the "
                   "torus main --harm certifies exactly")
    h.set_defaults(fn=cmd_hcert)
    p = sub.add_parser("spectrum", help="print the discrete harmonics of r_s in floating point")
    p.add_argument("wout")
    p.add_argument("--s", type=float, default=0.625)
    p.add_argument("--harmonics", nargs="+", default=["2,1", "2,0", "1,0", "3,1"])
    p.add_argument("--nu", type=int, default=64)
    p.add_argument("--nv", type=int, default=32)
    p.set_defaults(fn=cmd_spectrum)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
