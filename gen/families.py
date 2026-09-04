"""Run VMEC++ over a family of resolutions, for the convergence study.

[gen/convergence.py](convergence.py) measures the certified residual against
the grid spacing and against the mode set. That needs the same equilibrium
solved at several resolutions, which is what this produces: it reads one of
VMEC++'s own input files, overrides `ns_array`, `mpol` and `ntor`, and writes a
wout per member.

Each member is converged to `ftol` in the discrete force residual, so what
changes between them is the discretization and not how far the iteration ran.
The wout carries `fsqr`, `fsqz` and `fsql`, which is where to check that.

  python gen/families.py --input input.solovev --out DIR \\
         --ns 13,25,51,101,201 --mpol 12
  python gen/families.py --input input.li383_low_res --out DIR \\
         --ns 31 --mpol-ntor 4:3,6:4,8:6

VMEC++ is not a dependency of the checker or the generator; this is the only
tool here that runs a solver.
"""

import argparse
import pathlib
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, help="a VMEC++ input file")
    ap.add_argument("--out", required=True, help="where to write the wouts")
    ap.add_argument("--ns", default=None,
                    help="comma-separated radial resolutions")
    ap.add_argument("--mpol", type=int, default=None)
    ap.add_argument("--ntor", type=int, default=None)
    ap.add_argument("--mpol-ntor", default=None,
                    help="comma-separated mpol:ntor pairs, one member each")
    ap.add_argument("--ramp", action="store_true",
                    help="reach each resolution through the coarser ones, "
                    "which is what VMEC's multigrid is for: a fine grid "
                    "started cold often fails in the first iterations")
    ap.add_argument("--ftol", type=float, default=1.0e-16)
    ap.add_argument("--niter", type=int, default=60000)
    ap.add_argument("--prefix", default=None,
                    help="name the wouts with this stem")
    a = ap.parse_args()

    import vmecpp

    src = pathlib.Path(a.input)
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    stem = a.prefix or src.name.replace("input.", "")

    ns_list = [int(x) for x in a.ns.split(",")] if a.ns else [None]
    if a.mpol_ntor:
        spectra = [tuple(int(y) for y in p.split(":"))
                   for p in a.mpol_ntor.split(",")]
    else:
        spectra = [(a.mpol, a.ntor)]

    for ns in ns_list:
        for mpol, ntor in spectra:
            vi = vmecpp.VmecInput.from_file(src)
            if ns is not None:
                steps = ([x for x in ns_list if x is not None and x <= ns]
                         if a.ramp else [ns])
                vi.ns_array = steps
                vi.ftol_array = [a.ftol] * len(steps)
                vi.niter_array = [a.niter] * len(steps)
            if mpol is not None:
                vi.mpol = mpol
            if ntor is not None:
                vi.ntor = ntor
            tag = stem
            if ns is not None:
                tag += f"_ns{ns}"
            if mpol is not None:
                tag += f"_m{mpol}"
            if ntor is not None:
                tag += f"n{ntor}"
            try:
                res = vmecpp.run(vi, verbose=False)
            except Exception as e:  # noqa: BLE001
                print(f"{tag}: failed, {type(e).__name__}: {str(e)[:120]}")
                continue
            dst = out / f"wout_{tag}.nc"
            res.wout.save(dst)
            print(f"{dst.name}: ns={res.wout.ns} mnmax={res.wout.mnmax} "
                  f"fsqr={float(res.wout.fsqr):.2e}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
