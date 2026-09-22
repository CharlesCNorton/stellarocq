"""Invariance tests of VMEC++ whose answer a theorem of theories/ names.

Each test solves the same equilibrium twice along two code paths that the
reconstruction proves equivalent, and compares the two wouts coefficient by
coefficient and through their certificates.

  axisym   an axisymmetric input with ntor = 0 and with ntor = 4. Every
           toroidal derivative of an axisymmetric reconstruction is the zero
           expression (Identities.toroidal_terms_vanish), so the solution of
           the three-dimensional path has to be the axisymmetric one with
           every n /= 0 coefficient zero.
  lasym    a stellarator-symmetric input through the symmetric path and
           through the asymmetric one with zero antisymmetric boundary. A
           series whose coefficients vanish contributes nothing
           (Identities.assemble_value_zero), so the two runs have to agree,
           which is the reduction proximafusion/vmecpp#788 failed.
  gauge    a converged equilibrium restarted with its (0,0) lambda
           coefficient set to a nonzero value. Every angular derivative of
           lambda carries a factor m or n (Identities.lambda_gauge), so that
           coefficient drives nothing and the restart has to converge at once
           to the same equilibrium.
  nfp      a five-period stellarator solved over one period and over the
           whole torus, with the same toroidal sample points and the modes
           written in absolute toroidal numbers. The reconstruction reads a
           mode by its absolute number and nothing else (Physics.kern_arg), so
           the two runs describe one field and their coefficients have to
           agree, with every mode the full torus admits and the period does
           not coming out zero.

  python gen/oracle.py --out DIR [--tests axisym lasym gauge nfp]

VMEC++ is not a dependency of the checker or the generator; this is one of
the tools here that run a solver.
"""

import argparse
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def test_data():
    import vmecpp
    return pathlib.Path(vmecpp.__file__).parent / "cpp" / "vmecpp" / "test_data"


def solve(vi, dst, ftol=1.0e-15, restart=None):
    import numpy as np
    import vmecpp
    vi.ftol_array = np.full(len(vi.ns_array), ftol)
    vi.niter_array = np.full(len(vi.ns_array), 60000)
    res = vmecpp.run(vi, verbose=False, restart_from=restart)
    res.wout.save(dst)
    return res


def arrays(path):
    """The coefficient blocks of a wout as (ns, mnmax) arrays keyed by name."""
    import netCDF4
    import numpy as np
    d = netCDF4.Dataset(path)
    d.set_auto_mask(False)
    v = d.variables
    out = {"xm": np.asarray(v["xm"][:]).astype(int),
           "xn": np.asarray(v["xn"][:]).astype(int),
           "iotas": np.asarray(v["iotas"][:], dtype=float),
           "fsqr": float(v["fsqr"][:]), "niter": int(v["niter"][:])
           if "niter" in v else -1}
    for k in ("rmnc", "zmns", "lmns", "rmns", "zmnc", "lmnc"):
        if k in v:
            out[k] = np.asarray(v[k][:], dtype=float)
    d.close()
    return out


def match(a, b, ka, kb, sel_a, sel_b):
    """The largest difference between two coefficient blocks over a mode
    selection, relative to the largest coefficient of the first."""
    import numpy as np
    A, B = a[ka][:, sel_a], b[kb][:, sel_b]
    scale = float(np.abs(a[ka]).max()) or 1.0
    return float(np.abs(A - B).max()) / scale


def certify(wout, python, main, tmp, extra=""):
    """A point certificate of six nodes: the verdict and the float maxima."""
    cert = tmp / (pathlib.Path(wout).stem + ".txt")
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{cert}" --nodes 6 --nu 8 '
                  f'--nv 4 {extra}')
    if rc != 0:
        return "generator failed", None
    mx = [tuple(float(x) for x in m.groups())
          for m in re.finditer(r"\|r\|max = (\S+) (\S+) (\S+)", out)]
    rc, out = run(f'"{main}" "{cert}"')
    m = re.search(r"verdict: (\w+)", out)
    return (m.group(1) if m else "NONE"), mx


def report(name, rows):
    print(f"\n{name}")
    width = max(len(r[0]) for r in rows)
    for label, value, limit in rows:
        ok = value <= limit
        print(f"  {'ok  ' if ok else 'FAIL'} {label:<{width}}  {value:.3e}"
              f"  (at most {limit:.0e})")
    return all(v <= lim for _, v, lim in rows)


def axisym(out, python, main):
    import numpy as np
    import vmecpp
    base = test_data() / "circular_tokamak.json"
    dst = []
    for ntor in (0, 4):
        vi = vmecpp.VmecInput.from_file(base)
        mpol = vi.mpol
        rbc = np.zeros((mpol, 2 * ntor + 1))
        zbs = np.zeros((mpol, 2 * ntor + 1))
        rbc[:, ntor] = vi.rbc[:, 0]
        zbs[:, ntor] = vi.zbs[:, 0]
        vi.ntor = ntor
        vi.rbc, vi.zbs = rbc, zbs
        vi.raxis_c = np.zeros(ntor + 1)
        vi.raxis_c[0] = float(np.asarray(vi.raxis_c)[0]) if ntor == 0 else 6.0
        vi.zaxis_s = np.zeros(ntor + 1)
        vi.ns_array = np.array([17, 33])
        d = out / f"wout_axisym_ntor{ntor}.nc"
        solve(vi, d)
        dst.append(d)
    a, b = arrays(dst[0]), arrays(dst[1])
    n0 = b["xn"] == 0
    rows = []
    for k in ("rmnc", "zmns", "lmns"):
        rows.append((f"{k}: n /= 0 coefficients of the 3D run, of its largest",
                     float(np.abs(b[k][:, ~n0]).max()) / float(np.abs(b[k]).max()),
                     1e-12))
        rows.append((f"{k}: n = 0 coefficients against the ntor = 0 run",
                     match(a, b, k, k, slice(None), n0), 1e-8))
    rows.append(("iota on the half grid", float(np.abs(a["iotas"] - b["iotas"]).max()), 1e-12))
    va, ma = certify(dst[0], python, main, out)
    vb, mb = certify(dst[1], python, main, out)
    rows.append((f"certificates {va} and {vb}: largest residual, relative gap",
                 max(abs(x - y) / max(abs(x), 1e-300)
                     for p, q in zip(ma, mb) for x, y in zip(p, q))
                 if ma and mb and va == vb == "VALID" else 1.0, 1e-6))
    return report("axisym: an axisymmetric input through the three-dimensional path", rows)


def lasym(out, python, main):
    import numpy as np
    import vmecpp
    base = test_data() / "cth_like_fixed_bdy.json"
    dst = []
    for asym in (False, True):
        vi = vmecpp.VmecInput.from_file(base)
        vi.lasym = asym
        if asym:
            vi.rbs = np.zeros_like(vi.rbc)
            vi.zbc = np.zeros_like(vi.zbs)
            vi.raxis_s = np.zeros_like(vi.raxis_c)
            vi.zaxis_c = np.zeros_like(vi.zaxis_s)
        d = out / f"wout_lasym_{int(asym)}.nc"
        solve(vi, d)
        dst.append(d)
    a, b = arrays(dst[0]), arrays(dst[1])
    rows = []
    for k in ("rmnc", "zmns", "lmns"):
        rows.append((f"{k}: the asymmetric path against the symmetric one",
                     match(a, b, k, k, slice(None), slice(None)), 1e-8))
    for k in ("rmns", "zmnc", "lmnc"):
        rows.append((f"{k}: antisymmetric coefficients of the asymmetric run, "
                     f"of the largest symmetric one",
                     float(np.abs(b[k]).max()) / float(np.abs(b["rmnc"]).max()),
                     1e-12))
    rows.append(("iota on the half grid", float(np.abs(a["iotas"] - b["iotas"]).max()), 1e-10))
    va, ma = certify(dst[0], python, main, out, "--force-lasym")
    vb, mb = certify(dst[1], python, main, out)
    rows.append((f"certificates {va} and {vb}: largest residual, relative gap",
                 max(abs(x - y) / max(abs(x), 1e-300)
                     for p, q in zip(ma, mb) for x, y in zip(p, q))
                 if ma and mb and va == vb == "VALID" else 1.0, 1e-6))
    return report("lasym: a symmetric input through the asymmetric path", rows)


def gauge(out, python, main):
    import numpy as np
    import vmecpp
    base = test_data() / "solovev.json"
    vi = vmecpp.VmecInput.from_file(base)
    # a hot restart takes one grid, the state's
    vi.ns_array = np.array(vi.ns_array)[-1:]
    first = solve(vi, out / "wout_gauge_0.nc")
    # the (0,0) mode is the first of the list; the python wout holds the
    # coefficients as (mnmax, ns)
    k = [i for i, (m, n) in enumerate(zip(first.wout.xm, first.wout.xn))
         if m == 0 and n == 0][0]
    lm = np.array(first.wout.lmns)
    if lm.shape[0] != len(first.wout.xm):
        lm = lm.T
    lm[k, :] = 0.05
    first.wout.lmns = lm if np.array(first.wout.lmns).shape == lm.shape else lm.T
    second = solve(vi, out / "wout_gauge_1.nc", restart=first)
    a, b = arrays(out / "wout_gauge_0.nc"), arrays(out / "wout_gauge_1.nc")
    rows = []
    not00 = ~((b["xm"] == 0) & (b["xn"] == 0))
    for k_ in ("rmnc", "zmns"):
        rows.append((f"{k_}: after the restart against before",
                     match(a, b, k_, k_, slice(None), slice(None)), 1e-9))
    rows.append(("lmns: modes other than (0,0) after the restart against before",
                 match(a, b, "lmns", "lmns", not00, not00), 1e-9))
    rows.append(("iota on the half grid", float(np.abs(a["iotas"] - b["iotas"]).max()), 1e-12))
    rows.append((f"iterations of the restart ({second.wout.niter if hasattr(second.wout, 'niter') else '?'})",
                 float(getattr(second.wout, "niter", 0)), 50.0))
    print(f"  lmns(0,0) after the restart: {float(np.abs(np.asarray(b['lmns'])[:, ~not00]).max()):.3e}")
    va, ma = certify(out / "wout_gauge_0.nc", python, main, out)
    vb, mb = certify(out / "wout_gauge_1.nc", python, main, out)
    rows.append((f"certificates {va} and {vb}: largest residual, relative gap",
                 max(abs(x - y) / max(abs(x), 1e-300)
                     for p, q in zip(ma, mb) for x, y in zip(p, q))
                 if ma and mb and va == vb == "VALID" else 1.0, 1e-6))
    return report("gauge: a restart with the (0,0) lambda coefficient set", rows)


def nfp(out, python, main):
    import numpy as np
    import vmecpp
    base = test_data() / "cth_like_fixed_bdy.json"
    vi = vmecpp.VmecInput.from_file(base)
    period, ntor, mpol = int(vi.nfp), int(vi.ntor), int(vi.mpol)
    nzeta = int(vi.nzeta)
    dst5 = out / "wout_nfp_period.nc"
    solve(vi, dst5)
    # the same boundary and axis over the whole torus: mode n of the period
    # is mode period * n of the torus, and the torus is sampled at the same
    # points, period times as many per turn
    vt = vmecpp.VmecInput.from_file(base)
    vt.nfp = 1
    vt.ntor = period * ntor
    vt.nzeta = period * nzeta
    rbc = np.zeros((mpol, 2 * vt.ntor + 1))
    zbs = np.zeros((mpol, 2 * vt.ntor + 1))
    for n in range(-ntor, ntor + 1):
        rbc[:, vt.ntor + period * n] = vi.rbc[:, ntor + n]
        zbs[:, vt.ntor + period * n] = vi.zbs[:, ntor + n]
    raxis = np.zeros(vt.ntor + 1)
    zaxis = np.zeros(vt.ntor + 1)
    for n in range(ntor + 1):
        raxis[period * n] = vi.raxis_c[n]
        zaxis[period * n] = vi.zaxis_s[n]
    vt.rbc, vt.zbs = rbc, zbs
    vt.raxis_c, vt.zaxis_s = raxis, zaxis
    dst1 = out / "wout_nfp_torus.nc"
    solve(vt, dst1)
    a, b = arrays(dst5), arrays(dst1)
    # the torus modes that the period admits, in the period's order
    idx = {(int(m), int(n)): k for k, (m, n) in enumerate(zip(b["xm"], b["xn"]))}
    shared = [idx[(int(m), int(n))] for m, n in zip(a["xm"], a["xn"])]
    others = [k for k in range(len(b["xm"])) if k not in set(shared)]
    rows = []
    for k in ("rmnc", "zmns", "lmns"):
        scale = float(np.abs(a[k]).max()) or 1.0
        rows.append((f"{k}: the torus against the period on the period's modes",
                     float(np.abs(b[k][:, shared] - a[k]).max()) / scale, 1e-8))
        rows.append((f"{k}: modes of the torus the period does not admit, of "
                     f"the largest", float(np.abs(b[k][:, others]).max()) / scale,
                     1e-10))
    rows.append(("iota on the half grid",
                 float(np.abs(a["iotas"] - b["iotas"]).max()), 1e-10))
    va, ma = certify(dst5, python, main, out)
    vb, mb = certify(dst1, python, main, out)
    rows.append((f"certificates {va} and {vb}: largest residual, relative gap",
                 max(abs(x - y) / max(abs(x), 1e-300)
                     for p, q in zip(ma, mb) for x, y in zip(p, q))
                 if ma and mb and va == vb == "VALID" else 1.0, 1e-6))
    return report(f"nfp: a {period}-period stellarator over one period and "
                  f"over the torus ({len(a['xm'])} and {len(b['xm'])} modes)",
                  rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--tests", nargs="+", default=["axisym", "lasym", "gauge", "nfp"])
    ap.add_argument("--main",
                    default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    a = ap.parse_args()
    os.environ.setdefault("SKBUILD_EDITABLE_SKIP", "1")
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    ok = True
    for t in a.tests:
        ok = {"axisym": axisym, "lasym": lasym, "gauge": gauge, "nfp": nfp}[t](
            out, a.python, a.main) and ok
    print("\nevery invariance holds" if ok else "\nan invariance fails")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
