"""Rerun a wout's equilibrium at another resolution, from the wout alone.

An equilibrium whose input file is lost is not lost: the wout carries its
boundary, its axis, its profiles and its flux, which is everything a
fixed-boundary run needs. This rebuilds a VMEC++ input from those and runs it,
first at the wout's own resolution, where the result has to reproduce the wout
it came from, and then at whatever resolution is asked for. The first run is
the check on the second: a boundary transcribed with the wrong sign or the
wrong ordering of `n` would not reproduce the file, and the tool stops there.

  python gen/rerun.py wout_cma.nc --out DIR --mpol 9 --ntor 6 [--ns 51]

VMEC++ is not a dependency of the checker or the generator; this and
gen/families.py are the only tools here that run a solver.
"""

import argparse
import pathlib
import sys

import netCDF4
import numpy as np


def input_from_wout(path, template):
    """A VmecInput carrying the wout's boundary, axis, profiles and flux."""
    import vmecpp

    d = netCDF4.Dataset(path)
    d.set_auto_mask(False)
    v = d.variables
    g = lambda k: np.asarray(v[k][:], dtype=float)  # noqa: E731
    s = lambda k: (v[k][:].tobytes().decode().replace(chr(0), "").strip()  # noqa: E731
                   if k in v else "")
    nfp = int(v["nfp"][:])
    mpol, ntor = int(v["mpol"][:]), int(v["ntor"][:])
    ns = int(v["ns"][:])
    lasym = "lasym__logical__" in v and bool(int(v["lasym__logical__"][:]))
    xm, xn = g("xm").astype(int), g("xn").astype(int)
    rmnc, zmns = g("rmnc"), g("zmns")
    if lasym:
        rmns, zmnc = g("rmns"), g("zmnc")

    vi = vmecpp.VmecInput.from_file(template)
    vi.lasym = lasym
    vi.nfp = nfp
    vi.mpol, vi.ntor = mpol, ntor
    vi.phiedge = float(g("phi")[-1])
    vi.gamma = float(v["gamma"][:]) if "gamma" in v else 0.0
    vi.pmass_type = s("pmass_type") or "power_series"
    vi.am = g("am")
    vi.piota_type = s("piota_type") or "power_series"
    vi.ai = g("ai")
    vi.pcurr_type = s("pcurr_type") or "power_series"
    vi.ac = g("ac")
    for k in ("am_aux_s", "am_aux_f", "ai_aux_s", "ai_aux_f", "ac_aux_s",
              "ac_aux_f"):
        if k in v:
            setattr(vi, k, g(k))
    vi.curtor = float(v["ctor"][:]) if "ctor" in v else 0.0
    # which of iota and current is prescribed: a wout carries both arrays,
    # and the one the run used is the one that is not all zero
    vi.ncurr = 0 if np.any(g("ai") != 0) and not np.any(g("ac") != 0) else 1
    vi.lfreeb = False
    vi.mgrid_file = "NONE"

    # the boundary, from the last surface: rbc[m, n + ntor], with n in units
    # of the field period, as the input file writes it
    rbc = np.zeros((mpol, 2 * ntor + 1))
    zbs = np.zeros((mpol, 2 * ntor + 1))
    rbs = np.zeros((mpol, 2 * ntor + 1))
    zbc = np.zeros((mpol, 2 * ntor + 1))
    raxis_c = np.zeros(ntor + 1)
    zaxis_s = np.zeros(ntor + 1)
    raxis_s = np.zeros(ntor + 1)
    zaxis_c = np.zeros(ntor + 1)
    for k in range(len(xm)):
        m, n = int(xm[k]), int(xn[k]) // nfp
        if m >= mpol or abs(n) > ntor:
            continue
        rbc[m, n + ntor] = rmnc[-1][k]
        zbs[m, n + ntor] = zmns[-1][k]
        if lasym:
            rbs[m, n + ntor] = rmns[-1][k]
            zbc[m, n + ntor] = zmnc[-1][k]
        if m == 0 and n >= 0:
            raxis_c[n] = rmnc[0][k]
            zaxis_s[n] = zmns[0][k]
            if lasym:
                raxis_s[n] = rmns[0][k]
                zaxis_c[n] = zmnc[0][k]
    vi.rbc, vi.zbs = rbc, zbs
    vi.raxis_c, vi.zaxis_s = raxis_c, zaxis_s
    if lasym:
        vi.rbs, vi.zbc = rbs, zbc
        vi.raxis_s, vi.zaxis_c = raxis_s, zaxis_c
    else:
        vi.rbs = vi.zbc = None
        vi.raxis_s = vi.zaxis_c = None
    d.close()
    return vi, ns, mpol, ntor


def resize_modes(vi, mpol, ntor):
    """The same boundary in a larger mode array, the new entries zero."""
    old_m, old_n = vi.rbc.shape[0], (vi.rbc.shape[1] - 1) // 2

    def grow(a):
        if a is None:
            return None
        b = np.zeros((mpol, 2 * ntor + 1))
        for m in range(min(old_m, mpol)):
            for n in range(-min(old_n, ntor), min(old_n, ntor) + 1):
                b[m, n + ntor] = a[m, n + old_n]
        return b

    def grow_axis(a):
        if a is None:
            return None
        b = np.zeros(ntor + 1)
        b[: min(old_n, ntor) + 1] = a[: min(old_n, ntor) + 1]
        return b

    vi.rbc, vi.zbs = grow(vi.rbc), grow(vi.zbs)
    vi.rbs, vi.zbc = grow(vi.rbs), grow(vi.zbc)
    vi.raxis_c, vi.zaxis_s = grow_axis(vi.raxis_c), grow_axis(vi.zaxis_s)
    vi.raxis_s, vi.zaxis_c = grow_axis(vi.raxis_s), grow_axis(vi.zaxis_c)
    vi.mpol, vi.ntor = mpol, ntor


def compare(wout_path, out):
    """The rerun's coefficients against the source's, at the boundary and at
    mid radius, over the modes both carry."""
    d = netCDF4.Dataset(wout_path)
    d.set_auto_mask(False)
    v = d.variables
    xm, xn = np.asarray(v["xm"][:]).astype(int), np.asarray(v["xn"][:]).astype(int)
    rmnc, zmns = np.asarray(v["rmnc"][:]), np.asarray(v["zmns"][:])
    ns = int(v["ns"][:])
    d.close()
    w = out.wout
    xm2, xn2 = np.asarray(w.xm).astype(int), np.asarray(w.xn).astype(int)
    r2, z2 = np.asarray(w.rmnc), np.asarray(w.zmns)
    if r2.shape[0] != len(xm2):
        r2, z2 = r2.T, z2.T
    idx2 = {(int(m), int(n)): k for k, (m, n) in enumerate(zip(xm2, xn2))}
    worst = 0.0
    for row in (ns - 1, ns // 2):
        row2 = int(round(row * (w.ns - 1) / (ns - 1)))
        scale = float(np.max(np.abs(rmnc[row])))
        for k, (m, n) in enumerate(zip(xm, xn)):
            k2 = idx2.get((int(m), int(n)))
            if k2 is None:
                continue
            worst = max(worst, abs(r2[k2][row2] - rmnc[row][k]) / scale,
                        abs(z2[k2][row2] - zmns[row][k]) / scale)
    return worst


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--out", required=True)
    ap.add_argument("--mpol", type=int, default=None)
    ap.add_argument("--ntor", type=int, default=None)
    ap.add_argument("--ns", type=int, default=None)
    ap.add_argument("--template", default=None,
                    help="a VMEC++ input file to take the runtime settings "
                    "from; the default is the solovev example")
    ap.add_argument("--ftol", type=float, default=1.0e-14)
    ap.add_argument("--niter", type=int, default=100000)
    ap.add_argument("--tol", type=float, default=2e-2,
                    help="how far the rerun at the wout's own resolution may "
                    "sit from the wout, relative to its largest coefficient")
    ap.add_argument("--prefix", default=None)
    a = ap.parse_args()

    import vmecpp

    template = a.template or str(pathlib.Path(vmecpp.__file__).parent.parent
                                 / "vmecpp" / "examples" / "data"
                                 / "input.solovev")
    if not pathlib.Path(template).exists():
        raise SystemExit(f"no template input at {template}; give --template")
    vi, ns0, mpol0, ntor0 = input_from_wout(a.wout, template)
    ns = a.ns or ns0
    steps = sorted({s for s in (13, 25, ns) if s <= ns})
    vi.ns_array = np.array(steps)
    vi.ftol_array = np.array([a.ftol] * len(steps))
    vi.niter_array = np.array([a.niter] * len(steps))
    out_dir = pathlib.Path(a.out)
    out_dir.mkdir(parents=True, exist_ok=True)
    stem = a.prefix or pathlib.Path(a.wout).name.replace("wout_", "").replace(
        ".nc", "")

    print(f"rebuilt an input from {a.wout}: nfp={vi.nfp} mpol={mpol0} "
          f"ntor={ntor0} ns={ns0} ncurr={vi.ncurr} pmass={vi.pmass_type!r}")
    print(f"rerunning at the wout's own resolution to check the transcription")
    res = vmecpp.run(vi, verbose=False)
    gap = compare(a.wout, res)
    print(f"  fsqr={float(res.wout.fsqr):.2e}  worst coefficient gap "
          f"{gap:.3e} of the largest, at the boundary and mid radius")
    if gap > a.tol:
        raise SystemExit("the rerun does not reproduce the wout, so the "
                         "transcription of its boundary is not trusted; "
                         "nothing was written")
    dst = out_dir / f"wout_{stem}_ns{ns}_m{mpol0}n{ntor0}.nc"
    res.wout.save(dst)
    print(f"  wrote {dst.name}")

    if a.mpol is not None or a.ntor is not None:
        mpol, ntor = a.mpol or mpol0, a.ntor or ntor0
        resize_modes(vi, mpol, ntor)
        print(f"rerunning at mpol={mpol} ntor={ntor} ns={ns}")
        res = vmecpp.run(vi, verbose=False)
        dst = out_dir / f"wout_{stem}_ns{ns}_m{mpol}n{ntor}.nc"
        res.wout.save(dst)
        print(f"  fsqr={float(res.wout.fsqr):.2e}  mnmax={res.wout.mnmax}  "
              f"wrote {dst.name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
