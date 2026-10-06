"""The rippled circular tokamak of gen/resonance.py in SPEC: the current sheet
an ideal interface at the rational surface carries, and the island a relaxed
volume opens there, against the amplitude of the ripple.

The tokamak is VMEC++'s circular one, R0 = 6 and a = 2, with a (1,1) boundary
ripple of amplitude A and no pressure, and VMEC++'s transform is
iota = 0.9 - 0.64 s, which is 1/2 on the surface enclosing 0.625 of the
toroidal flux. SPEC (the Stepped Pressure Equilibrium Code, Hudson et al.,
Phys. Plasmas 19, 112502 (2012)) builds the field from Beltrami volumes
separated by ideal interfaces, and gives two answers the certificates of
gen/resonance.py can be read against.

  ideal    two volumes whose interface encloses 0.625 of the flux, the
           transform held at 1/2 on both sides of it and at 0.26 on the
           boundary (Lconstraint 1). The interface is a flux surface by
           construction, and the jump of the covariant tangential field across
           it is the surface current it carries, harmonic by harmonic. The
           (2,1) jump is the sheet the ripple forces, linear in A.
  relaxed  three volumes with interfaces at 0.35 and 0.85 of the flux and the
           transform held there at VMEC++'s profile, so that iota = 1/2 falls
           inside the middle volume, whose Beltrami field is free to
           reconnect. SPEC's field-line tracing (pp00aa) follows trajectories
           launched across that volume; a trajectory is in the island when its
           poloidal angle, less half a turn per toroidal transit, stays within
           half a turn of where it started, and the island's width is the
           largest radial excursion of such a trajectory, which grows as the
           square root of A (Hypotheses.island_width).

  python gen/spec_sheet.py --xspec PATH --out DIR --ripple 0.03,0.015,0.0075

needs h5py and numpy, and prints both ladders with the ratio of each entry to
the next.
"""

import argparse
import os
import pathlib
import subprocess
import sys
import time

S_RATIONAL = 0.625
IOTA = (0.9, -0.64)
EDGE_IOTA = IOTA[0] + IOTA[1]

NUMERIC = """&numericlist
 Linitialize =         1
 Ndiscrete   =         2
 Nquad       =        -1
 iMpol       =        -4
 iNtor       =        -4
 Lsparse     =         0
 Lsvdiota    =         1
 imethod     =         3
 iorder      =         2
 iprecon     =         1
 iotatol     =  -1.000000000000000E+00
/
&locallist
 LBeltrami   =         4
 Linitgues   =         1
/
&globallist
 Lfindzero   =         2
 escale      =   0.000000000000000E+00
 pcondense   =   4.000000000000000E+00
 forcetol    =   1.000000000000000E-12
 c05xtol     =   1.000000000000000E-12
 c05factor   =   1.000000000000000E-04
 LreadGF     =         F
 opsilon     =   1.000000000000000E+00
 epsilon     =   1.000000000000000E+00
 upsilon     =   1.000000000000000E+00
/
"""


def f(v):
    return f"{v: .15E}"


def iota_at(s):
    return IOTA[0] + IOTA[1] * s


def write_input(path, amp, kind, mpol, ntor, lrad, ppts=0.0, nppts=0, nptrj=None):
    """A SPEC input for the rippled tokamak; kind is "ideal" or "relaxed"."""
    if kind == "ideal":
        tflux = [S_RATIONAL, 1.0]
        iota = [0.0, 0.5, EDGE_IOTA]
    else:
        tflux = [0.35, 0.85, 1.0]
        iota = [0.0] + [iota_at(s) for s in tflux]
    nvol = len(tflux)
    L = ["&physicslist",
         " Igeometry   =         3", " Istellsym   =         1", " Lfreebound  =         0",
         f" phiedge     = {f(1.0)}", f" curtor      = {f(0.0)}", f" curpol      = {f(0.0)}",
         f" gamma       = {f(0.0)}", " Nfp         =         1", f" Nvol        = {nvol:9d}",
         f" Mpol        = {mpol:9d}", f" Ntor        = {ntor:9d}",
         " Lrad        = " + " ".join(f"{lrad:9d}" for _ in range(nvol)),
         " tflux       = " + " ".join(f(x) for x in tflux),
         " pflux       = " + " ".join(f(0.0) for _ in range(nvol)),
         " helicity    = " + " ".join(f(0.0) for _ in range(nvol)),
         f" pscale      = {f(0.0)}", " Ladiabatic  =         0",
         " pressure    = " + " ".join(f(0.0) for _ in range(nvol)),
         " adiabatic   = " + " ".join(f(0.0) for _ in range(nvol)),
         " mu          = " + " ".join(f(0.0) for _ in range(nvol)),
         " Lconstraint =         1",
         " iota        = " + " ".join(f(x) for x in iota),
         " oita        = " + " ".join(f(x) for x in iota),
         f" mupftol     = {f(1e-12)}", " mupfits     =       128",
         f" Rac         = {f(6.0)} " + " ".join(f(0.0) for _ in range(ntor)),
         " Zas         = " + " ".join(f(0.0) for _ in range(ntor + 1)),
         " Ras         = " + " ".join(f(0.0) for _ in range(ntor + 1)),
         " Zac         = " + " ".join(f(0.0) for _ in range(ntor + 1))]
    for m in range(mpol + 1):
        for n in range(-ntor, ntor + 1):
            if m == 0 and n < 0:
                continue
            rbc = zbs = 0.0
            if (m, n) == (0, 0):
                rbc = 6.0
            elif (m, n) == (1, 0):
                rbc = zbs = 2.0
            elif (m, n) == (1, 1):
                rbc = zbs = amp
            L.append(f"Rbc({n},{m}) = {f(rbc)} Zbs({n},{m}) = {f(zbs)} "
                     f"Rbs({n},{m}) = {f(0.0)} Zbc({n},{m}) = {f(0.0)}")
    L.append("/")
    nptrj = nptrj or [2 * lrad] * nvol
    diag = ["&diagnosticslist", f" odetol      = {f(1e-9)}",
            f" absreq      = {f(1e-8)}", f" relreq      = {f(1e-8)}",
            f" absacc      = {f(1e-4)}", f" epsr        = {f(1e-8)}",
            f" nPpts       = {nppts:9d}", f" Ppts        = {f(ppts)}",
            " nPtrj       = " + " ".join(f"{x:6d}" for x in nptrj),
            " LHevalues   =         F", " LHevectors  =         F", "/", "&screenlist", "/"]
    pathlib.Path(path).write_text("\n".join(L) + "\n" + NUMERIC + "\n".join(diag) + "\n")


def run_spec(xspec, path, threads):
    env = dict(os.environ, OMP_NUM_THREADS=str(threads))
    h5 = pathlib.Path(str(path) + ".h5")
    if h5.exists():
        h5.unlink()
    t0 = time.time()
    p = subprocess.run([xspec, pathlib.Path(path).name], cwd=pathlib.Path(path).parent, env=env,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    pathlib.Path(str(path) + ".log").write_text(p.stdout)
    if p.returncode != 0 or not h5.exists():
        raise SystemExit(f"xspec failed on {path}:\n{p.stdout[-2000:]}")
    return time.time() - t0


def sheet(h5path):
    """The (2,1) jump of B_theta and B_zeta across the interface, and the
    force error SPEC reports."""
    import h5py
    import numpy as np

    with h5py.File(h5path, "r") as fh:
        o = fh["output"]
        im = np.asarray(o["im"], int)
        inn = np.asarray(o["in"], int)
        bte = np.asarray(o["Btemn"])  # [volume][side][mode]
        bze = np.asarray(o["Bzemn"])
        ferr = float(np.asarray(o["ForceErr"]).ravel()[0])
    k = [i for i in range(len(im)) if im[i] == 2 and inn[i] == 1][0]
    return bte[1, 0, k] - bte[0, 1, k], bze[1, 0, k] - bze[0, 1, k], ferr


def island(h5paths, vol=2):
    """The largest radial excursion, in the volume's radial coordinate, of a
    trajectory trapped in the (2,1) island, over the given runs; and the
    number of trapped trajectories."""
    import h5py
    import numpy as np

    width, trapped = 0.0, 0
    for p in h5paths:
        with h5py.File(p, "r") as fh:
            t = np.asarray(fh["poincare"]["t"])
            s = np.asarray(fh["poincare"]["s"])
            ok = np.asarray(fh["poincare"]["success"]).ravel()
            nptrj = np.asarray(fh["input"]["diagnostics"]["nPtrj"]).ravel()
        # trajectories are stored volume by volume, nPtrj + 1 of them in each
        # volume past the first (the innermost starts off the axis)
        counts = [int(nptrj[0])] + [int(x) + 1 for x in nptrj[1:]]
        start = sum(counts[:vol - 1])
        sel = range(start, start + counts[vol - 1])
        for i in sel:
            if not ok[i]:
                continue
            # [trajectory, transit, toroidal plane]: the section at zeta = 0
            th = t[i, :, 0]
            ss = s[i, :, 0]
            # less half a turn per transit first, since unwrapping steps of
            # exactly half a turn is ambiguous
            phase = th - np.pi * np.arange(len(th))
            dev = np.unwrap(phase) - phase[0]
            if np.abs(dev).max() < np.pi:
                trapped += 1
                width = max(width, float(ss.max() - ss.min()))
    return width, trapped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--xspec", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--ripple", default="0.03,0.015,0.0075")
    ap.add_argument("--mpol", type=int, default=8)
    ap.add_argument("--ntor", type=int, default=2)
    ap.add_argument("--lrad", type=int, default=8)
    ap.add_argument("--nppts", type=int, default=400)
    ap.add_argument("--nptrj", type=int, default=240,
                    help="trajectories across the middle volume of the relaxed case")
    ap.add_argument("--threads", type=int, default=4)
    ap.add_argument("--skip-relaxed", action="store_true")
    a = ap.parse_args()
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    amps = [float(x) for x in a.ripple.split(",")]
    rows = []
    for amp in amps:
        tag = f"{amp:.6g}".replace(".", "p")
        ideal = out / f"ideal_{tag}_L{a.lrad}.sp"
        write_input(ideal, amp, "ideal", a.mpol, a.ntor, a.lrad)
        dt = run_spec(a.xspec, ideal, a.threads)
        jt, jz, ferr = sheet(str(ideal) + ".h5")
        row = {"amp": amp, "jt": jt, "jz": jz, "ferr": ferr, "t_ideal": dt}
        if not a.skip_relaxed:
            paths = []
            for ppts in (0.0, 0.25):
                rel = out / f"relaxed_{tag}_L{a.lrad}_p{int(100 * ppts)}.sp"
                write_input(rel, amp, "relaxed", a.mpol, a.ntor, a.lrad, ppts=ppts,
                            nppts=a.nppts, nptrj=[2 * a.lrad, a.nptrj, 2 * a.lrad])
                run_spec(a.xspec, rel, a.threads)
                paths.append(str(rel) + ".h5")
            row["width"], row["trapped"] = island(paths)
        rows.append(row)
        print(f"ripple {amp:.6g}: sheet [[B_theta]]_21 {jt:+.6e} [[B_zeta]]_21 {jz:+.6e} "
              f"(force error {ferr:.1e}, {dt:.0f} s)"
              + (f"; island width {row['width']:.5f} from {row['trapped']} trapped trajectories"
                 if "width" in row else ""), flush=True)
    for r0, r1 in zip(rows, rows[1:]):
        line = (f"{r0['amp']:.6g} / {r1['amp']:.6g}: sheet ratio {r0['jt'] / r1['jt']:.4f}")
        if "width" in r0 and r1.get("width"):
            line += f", island width ratio {r0['width'] / r1['width']:.4f}"
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
