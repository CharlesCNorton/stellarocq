"""The Boozer stream function of one surface, from certified harmonics.

The Boozer angles differ from VMEC's by a stream function w:

  B_u = I(s) + d_u w,   B_v = G(s) + d_v w,
  p = w / (G + iota I),  theta_B = u + lambda + iota p,  zeta_B = v + p.

Two things have to hold for that to mean anything, and both are certified here
rather than assumed. w exists on a surface only when the covariant components
have no curl there,

  d_u B_v - d_v B_u = mu0 sqrt(g) J^s = 0,

which is the same quantity the force residual carries, so its harmonics are
enclosed by the same covering that supplies w. And the coefficients themselves
are angular integrals of the covariant components against a kernel, which is
what `--covariant` carries and `main --integrate` encloses.

For a cosine series f = sum f_mn cos(mu - nv) over the whole angular torus the
projection integrals are f_mn times 2 pi^2, or 4 pi^2 at m = n = 0, and

  w_mn = a_mn / m   (m /= 0),      w_mn = -c_mn / n   (m = 0, n /= 0)

with a and c the coefficients of B_u and B_v. Both expressions have to give the
same w wherever both apply, and their difference is n a_mn + m c_mn, which
vanishes exactly when the surface current harmonic does.

  python gen/boozer.py wout.nc --node 22 --modes 1,0 2,0 3,0

`--defect` and `--spectrum` carry it the rest of the way. The stream function
has no closed form as an expression, so it is computed in floating point and
written into the certificate as data; `--defect` then bounds how far it is from
satisfying the two relations that define it, at every angle of the surface, and
`--spectrum` certifies the harmonics of |B| in the Boozer angles those data
give. The Jacobian of the angle map comes back with them, and its integral has
to be 4 pi^2 because the map is a bijection of the torus, which is a check the
run makes on itself.

Everything up to the integrals is inside the checker. Dividing them by 2 pi^2
and by the mode number happens here, in floating point rounded outward, which
is the one step this tool takes on its own.
"""

import argparse
import math
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def div_out(iv, d):
    """The interval divided by a positive constant, rounded outward."""
    lo, hi = iv
    lo, hi = lo / d, hi / d
    return (math.nextafter(lo, -math.inf), math.nextafter(hi, math.inf))


def harmonics(wout, node, nu, nv, m, n, kind, main, python, tmp, surface):
    """The three certified integrals of one projection."""
    src = tmp / f"cv_{kind}_{m}_{n}.txt"
    dst = tmp / f"cv_{kind}_{m}_{n}_c.txt"
    flag = "--covariant" if kind == "cos" else "--covariant-sin"
    extra = f" --nv {nv} --surface" if surface else ""
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" --cells --node {node} '
                  f'--nu {nu}{extra} {flag} {m},{n}')
    if rc != 0:
        raise SystemExit(f"generator failed:\n{out}")
    rc, out = run(f'"{main}" --tighten "{src}" "{dst}"')
    if rc != 0:
        raise SystemExit(f"tighten failed:\n{out}")
    rc, out = run(f'"{main}" --integrate "{dst}"')
    if rc != 0:
        raise SystemExit(f"integrate failed:\n{out}")
    got = {}
    for label in ("B_u k", "B_v k", "mu0 sqrtg J^s k"):
        mm = re.search(r"^\s+" + re.escape(label) + r"\s+exact\s+(\S+)"
                       r"\s+(\S+)", out, re.M)
        if not mm:
            raise SystemExit(f"no exact endpoints for {label} in:\n{out}")
        got[label] = (float.fromhex(mm.group(1)), float.fromhex(mm.group(2)))
    return got


def show(name, iv, note=""):
    print(f"  {name:<16} [{iv[0]:+.9e}, {iv[1]:+.9e}]  {note}")


def worst_by_component(cert):
    """The largest cell bound of each of the three components."""
    worst = [0.0, 0.0, 0.0]
    i = 0
    inside = False
    for line in pathlib.Path(cert).read_text().splitlines():
        if line.startswith("CELLS"):
            inside, i = True, 0
            continue
        if inside:
            f = line.split()
            if len(f) >= 8 and all(x.lstrip("-").isdigit() for x in f[:8]):
                v = float(f[6]) * 2.0 ** float(f[7])
                worst[i % 3] = max(worst[i % 3], v)
                i += 1
            elif line.startswith("NODE"):
                inside = False
    return worst


def one_covering(wout, node, nu, nv, surface, extra, main, python, tmp, tag,
                 labels):
    """Generate, tighten and integrate one covering; return both readings."""
    src = tmp / f"{tag}.txt"
    dst = tmp / f"{tag}_c.txt"
    ex = f" --nv {nv} --surface" if surface else ""
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" --cells --node {node} '
                  f'--nu {nu}{ex} {extra}')
    if rc != 0:
        raise SystemExit(f"generator failed:\n{out}")
    rc, out = run(f'"{main}" --tighten "{src}" "{dst}"')
    if rc != 0:
        raise SystemExit(f"tighten failed:\n{out}")
    bounds = worst_by_component(dst)
    rc, out = run(f'"{main}" --integrate "{dst}"')
    if rc != 0:
        raise SystemExit(f"integrate failed:\n{out}")
    ivs = {}
    for label in labels:
        mm = re.search(r"^\s+" + re.escape(label) + r"\s+exact\s+(\S+)"
                       r"\s+(\S+)", out, re.M)
        if not mm:
            raise SystemExit(f"no exact endpoints for {label} in:\n{out}")
        ivs[label] = (float.fromhex(mm.group(1)), float.fromhex(mm.group(2)))
    return bounds, ivs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--node", type=int, required=True)
    ap.add_argument("--nu", type=int, default=512)
    ap.add_argument("--nv", type=int, default=64)
    ap.add_argument("--surface", action="store_true",
                    help="give the toroidal angle width, which a "
                    "three-dimensional equilibrium needs")
    ap.add_argument("--modes", nargs="+", default=["1,0"],
                    help="the (m,n) to project onto")
    ap.add_argument("--sin", action="store_true",
                    help="project onto sin(mu - nv) as well, which a "
                    "non-stellarator-symmetric equilibrium needs")
    ap.add_argument("--defect", action="store_true",
                    help="bound how far the stream function the certificate "
                    "carries is from satisfying its two relations")
    ap.add_argument("--spectrum", nargs="*", default=None,
                    metavar="M,N",
                    help="certify the harmonics of |B| in the Boozer angles")
    ap.add_argument(
        "--main",
        default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    a = ap.parse_args()

    # a three-dimensional equilibrium covered by curves is not covered
    import netCDF4
    import numpy as np
    with netCDF4.Dataset(a.wout) as d:
        d.set_auto_mask(False)
        three_d = bool((np.asarray(d.variables["xn"][:]) != 0).any())
    if three_d and not a.surface:
        msg = ("this equilibrium is three-dimensional, so these are integrals "
               "over the whole torus: give --surface, since a covering by "
               "curves at sample toroidal angles is not a covering of the "
               "surface")
        raise SystemExit(msg)

    tmp = pathlib.Path(tempfile.mkdtemp(prefix="booz_"))
    two_pi2 = 2.0 * math.pi * math.pi
    four_pi2 = 2.0 * two_pi2

    print(f"{a.wout} node {a.node}")
    print("\nthe flux functions, from the m = n = 0 projection:")
    z = harmonics(a.wout, a.node, a.nu, a.nv, 0, 0, "cos", a.main, a.python,
                  tmp, a.surface)
    I = div_out(z["B_u k"], four_pi2)
    G = div_out(z["B_v k"], four_pi2)
    show("I(s)", I)
    show("G(s)", G)
    show("current", z["mu0 sqrtg J^s k"],
         "and exactly zero by periodicity, whatever the covering")

    print("\nper mode: the coefficients of B_u and B_v, the defect of the "
          "relation\nbetween them, and the stream function they give")
    for spec in a.modes:
        m, n = (int(x) for x in spec.split(","))
        for kind in (("cos", "sin") if a.sin else ("cos",)):
            h = harmonics(a.wout, a.node, a.nu, a.nv, m, n, kind, a.main,
                          a.python, tmp, a.surface)
            norm = four_pi2 if (m == 0 and n == 0) else two_pi2
            av = div_out(h["B_u k"], norm)
            cv = div_out(h["B_v k"], norm)
            print(f"\n  (m, n) = ({m}, {n}), against {kind}(mu - nv):")
            show("a = B_u", av)
            show("c = B_v", cv)
            # n a + m c has to vanish, and the surface current is why
            lo = min(n * av[0] + m * cv[0], n * av[1] + m * cv[1],
                     n * av[0] + m * cv[1], n * av[1] + m * cv[0])
            hi = max(n * av[0] + m * cv[0], n * av[1] + m * cv[1],
                     n * av[0] + m * cv[1], n * av[1] + m * cv[0])
            ok = lo <= 0.0 <= hi
            show("n a + m c", (lo, hi),
                 "brackets zero" if ok else "DOES NOT bracket zero")
            if m != 0:
                show("w = a / m", div_out(av, float(m)))
            elif n != 0:
                w = div_out(cv, float(-n))
                show("w = -c / n", w)
            else:
                print("  w is undefined at m = n = 0, where the gauge is free")
    if a.defect:
        print("\nthe stream function the certificate carries, against the two "
              "relations\nthat define it, at every angle of the surface:")
        bounds, _ = one_covering(
            a.wout, a.node, a.nu, a.nv, a.surface, "--stream-defect", a.main,
            a.python, tmp, "defect",
            ["w_u defect", "w_v defect", "mu0 sqrtg J^s"])
        for nm, v in zip(("d_u w - (B_u - I)", "d_v w - (B_v - G)",
                          "mu0 sqrt(g) J^s"), bounds, strict=True):
            print(f"  {nm:<20} at most {v:.6e}")
        print("  The third is what has to vanish for any stream function to "
              "exist, and\n  the first two are how far this one is from "
              "being it.")

    if a.spectrum is not None:
        two_pi2_ = 2.0 * math.pi * math.pi
        print("\nthe harmonics of |B| in the Boozer angles:")
        for spec in (a.spectrum or ["0,0"]):
            m, n = (int(x) for x in spec.split(","))
            _, ivs = one_covering(
                a.wout, a.node, a.nu, a.nv, a.surface, f"--boozer {m},{n}",
                a.main, a.python, tmp, f"bz_{m}_{n}",
                ["|B| cos J", "|B| sin J", "J"])
            norm = (2.0 * two_pi2_) if (m == 0 and n == 0) else two_pi2_
            print(f"\n  (m, n) = ({m}, {n}):")
            show("B cos", div_out(ivs["|B| cos J"], norm))
            show("B sin", div_out(ivs["|B| sin J"], norm))
            jac = ivs["J"]
            ok = jac[0] <= 2.0 * two_pi2_ <= jac[1]
            show("int J", jac,
                 "brackets 4 pi^2" if ok else "DOES NOT bracket 4 pi^2")

    if not a.defect and a.spectrum is None:
        print("\n--defect bounds how far the stream function is from its two "
              "relations,\nand --spectrum certifies the harmonics of |B| in "
              "the Boozer angles it gives.")


if __name__ == "__main__":
    main()
