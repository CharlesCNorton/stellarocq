"""The certified harmonics of the residual on one surface against the radial
resolution, for a tokamak with a boundary ripple.

A rational surface is where a nested-surface equilibrium can fail to exist: a
resonant harmonic of the force that is driven there has no regular solution.
This runs VMEC++ on the circular tokamak of its own test data with a chosen
iota profile and one boundary harmonic, at a series of radial resolutions,
and certifies the harmonics of the residual on the surface at a chosen radius
with `main --project --spectrum`, which is Project.harm_encloses. A harmonic
that falls fourfold per doubling of ns is resolved at second order; one that
stays put is an obstruction the solver's representation cannot remove.

  python gen/resonance.py --out DIR --ripple 1,1,0.03 --iota 0.9,-0.64 \\
         --s 0.625 --ns 65,129,257 --modes 2,0 1,1 2,1 3,1

With iota = 0.9 - 0.64 s the surface s = 0.625 carries iota = 1/2, and a
(1,1) ripple drives the (2,1) sideband there through toroidal coupling. With
--iota 0.62,-0.1 no rational of order below seven sits near it, which is the
control. VMEC++ is not a dependency of the checker or the generator; this,
gen/families.py and gen/rerun.py are the tools here that run a solver.
"""

import argparse
import os
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def solve(base, out, ripple, iota, pressure, ftol, ns, mpol, ntor):
    """One VMEC++ run, ramped through the coarser grids; returns the wout."""
    import numpy as np
    import vmecpp

    vi = vmecpp.VmecInput.from_file(base)
    vi.mpol, vi.ntor = mpol, ntor
    vi.ai = np.array(iota)
    vi.pmass_type = "power_series"
    vi.am = np.array([pressure, -pressure])
    vi.pres_scale = 1.0
    rbc = np.zeros((mpol, 2 * ntor + 1))
    zbs = np.zeros((mpol, 2 * ntor + 1))
    rbc[0, ntor] = 6.0
    rbc[1, ntor] = 2.0
    zbs[1, ntor] = 2.0
    if ripple is not None:
        m, n, amp = ripple
        rbc[m, ntor + n] = amp
        zbs[m, ntor + n] = amp
    vi.rbc, vi.zbs = rbc, zbs
    vi.raxis_c = np.zeros(ntor + 1)
    vi.raxis_c[0] = 6.0
    vi.zaxis_s = np.zeros(ntor + 1)
    steps = [x for x in (17, 33, 65, 129, 257, 513) if x < ns] + [ns]
    vi.ns_array = np.array(steps)
    vi.ftol_array = np.full(len(steps), ftol)
    vi.niter_array = np.full(len(steps), 60000)
    vi.nstep = 1000
    t0 = time.time()
    res = vmecpp.run(vi, verbose=False)
    dst = out / f"wout_ns{ns}.nc"
    res.wout.save(dst)
    print(f"  ns={ns}: fsqr={float(res.wout.fsqr):.2e} "
          f"iter={getattr(res.wout, 'niter', -1)} {time.time() - t0:.0f} s",
          flush=True)
    return dst


def harmonics(wout, node, nu, nv, main, python, tmp):
    """The certified cosine and sine harmonics of the three components."""
    cert = tmp / f"{wout.stem}_n{node}.txt"
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{cert}" --node {node} '
                  f'--nu {nu} --nv {nv}')
    if rc != 0:
        raise SystemExit(f"generator failed:\n{out}")
    scale = float(re.search(r"reference B\^2 scale (\S+)", out).group(1))
    rc, out = run(f'"{main}" --project --spectrum "{cert}"')
    if rc != 0 or "verdict: VALID" not in out:
        raise SystemExit(f"the point certificate was not established:\n{out}")
    got = {}
    for mm in re.finditer(
            r"^\s+\((-?\d+),(-?\d+)\) (cos|sin)  r_s \[(\S+), (\S+)\]  "
            r"r_u \[(\S+), (\S+)\]  r_v \[(\S+), (\S+)\]", out, re.M):
        key = (int(mm.group(1)), int(mm.group(2)), mm.group(3))
        got[key] = tuple(float(mm.group(i)) for i in range(4, 10))
    return got, scale


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, help="where the wouts go")
    ap.add_argument("--ripple", default=None, metavar="M,N,AMP",
                    help="one boundary harmonic, in metres on a minor radius "
                    "of two")
    ap.add_argument("--iota", default="0.9,-0.64",
                    help="the prescribed iota profile, a0 + a1 s")
    ap.add_argument("--pressure", type=float, default=0.0,
                    help="p = P (1 - s) in pascal")
    ap.add_argument("--ftol", type=float, default=1.0e-15)
    ap.add_argument("--mpol", type=int, default=8)
    ap.add_argument("--ntor", type=int, default=4)
    ap.add_argument("--ns", default="33,65,129,257")
    ap.add_argument("--s", type=float, default=0.625,
                    help="the surface; it has to be a node of every grid")
    ap.add_argument("--nu", type=int, default=64)
    ap.add_argument("--nv", type=int, default=32)
    ap.add_argument("--modes", nargs="+", default=["2,0", "1,1", "2,1", "3,1"],
                    help="the harmonics to tabulate")
    ap.add_argument("--component", default="r_s",
                    choices=["r_s", "r_u", "r_v"])
    ap.add_argument("--kernel", default=None, choices=["cos", "sin"],
                    help="cosine for r_s and sine for r_u and r_v unless "
                    "given, which is what stellarator symmetry leaves")
    ap.add_argument("--base", default=None,
                    help="the VMEC++ input to start from; the default is "
                    "circular_tokamak.json of its test data")
    ap.add_argument("--main",
                    default=str(ROOT / "extract" / "_build" / "default"
                                / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    a = ap.parse_args()

    os.environ.setdefault("SKBUILD_EDITABLE_SKIP", "1")
    import vmecpp

    base = a.base or str(pathlib.Path(vmecpp.__file__).parent / "cpp"
                         / "vmecpp" / "test_data" / "circular_tokamak.json")
    if not pathlib.Path(base).exists():
        raise SystemExit(f"no base input at {base}; give --base")
    ripple = None
    if a.ripple:
        m, n, amp = a.ripple.split(",")
        ripple = (int(m), int(n), float(amp))
    iota = [float(x) for x in a.iota.split(",")]
    kernel = a.kernel or ("cos" if a.component == "r_s" else "sin")
    col = {"r_s": 0, "r_u": 2, "r_v": 4}[a.component]
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    tmp = out / "certs"
    tmp.mkdir(exist_ok=True)

    print(f"circular tokamak, iota = {iota[0]:g} {iota[1]:+g} s, "
          f"p = {a.pressure:g} (1 - s), ripple {a.ripple or 'none'}, "
          f"mpol {a.mpol} ntor {a.ntor}")
    print(f"the {kernel} harmonics of {a.component} at s = {a.s:g}, "
          f"iota = {iota[0] + iota[1] * a.s:.4f}, over {a.nu} by {a.nv} angles")
    modes = [tuple(int(x) for x in mn.split(",")) for mn in a.modes]
    rows = []
    for ns in (int(x) for x in a.ns.split(",")):
        node = round((ns - 1) * a.s)
        if abs(node - (ns - 1) * a.s) > 1e-9:
            raise SystemExit(f"s = {a.s} is not a node of ns = {ns}")
        wout = solve(base, out, ripple, iota, a.pressure, a.ftol, ns,
                     a.mpol, a.ntor)
        got, scale = harmonics(wout, node, a.nu, a.nv, a.main, a.python, tmp)
        rows.append((ns, scale, got))

    head = " ".join(f"{'H(%d,%d)' % mn:>22}" for mn in modes)
    print(f"\n{'ns':>4} {'B^2':>9} {head}")
    prev = None
    for ns, scale, got in rows:
        cells = []
        for mn in modes:
            v = got.get((mn[0], mn[1], kernel))
            if v is None:
                cells.append(f"{'absent':>22}")
                continue
            lo, hi = v[col], v[col + 1]
            mid = 0.5 * (lo + hi)
            ratio = ""
            if prev is not None and prev.get((mn[0], mn[1], kernel)):
                p = prev[(mn[0], mn[1], kernel)]
                pm = 0.5 * (p[col] + p[col + 1])
                if mid != 0.0:
                    ratio = f" x{abs(pm / mid):4.1f}"
            cells.append(f"{mid:+11.3e}{'+-':>2}{0.5 * (hi - lo):7.1e}{ratio:>6}")
        print(f"{ns:4d} {scale:9.3e} " + " ".join(cells))
        prev = got
    print("\nEach entry is the midpoint and half-width of the certified "
          "enclosure, and the factor\nby which the previous grid's value "
          "exceeds it. Four per doubling of ns is second\norder; a factor "
          "near one is a harmonic the radial grid does not resolve.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
