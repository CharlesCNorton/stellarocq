"""The Mercier criterion of one surface, end to end from a wout.

Four coverings carry the integrands `mercier.f90` combines:

  --mercier a           tpp, tbb, tjb      the half-grid integrands
  --mercier b           tjj
  --radial --geometry   V''                off the free-radius reconstruction
  --radial --shear      iota', the current gradient, mu0 p'

and phips and signgs come from the wout. This writes the four and a run file
naming them, and hands that to `main --mercier-run`: the checker integrates
each covering's integrands over the whole angular torus itself
(theories/Integrate.v, integ2_torus) and assembles DShear, DCurr, DWell, DGeod
and DMerc from those integrals (theories/MercierRun.v, merc_run). No
enclosure passes from one run to another.

  python gen/mercier.py wout.nc --node 22 [--nu 512] [--main PATH]

The paper's case is up_down_asym of VMEC++'s test data solved at 17 surfaces
(ns_array 5, 11, 17 to ftol 1e-11), at node 2, s = 0.125:

  python gen/mercier.py wout_up_down_asym.nc --node 2 --nu 2048 --main PATH

`--write FILE` keeps the run file, which with the four coverings it names is
what another party would re-check.

`--profile` does every interior surface at once. The four coverings each carry
every node, so a whole profile costs four coverings rather than four per
surface, and what comes out is the criterion as a function of the radius:
where it is negative, by how much, and where the covering cannot decide.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"

# the ten numbers the terms are evaluated at, in the slot order
# theories/Mercier.v fixes, as `main --mercier-run` prints them
INPUTS = ["tpp", "tbb", "tjb", "tjj", "V''", "mu0 p'", "iota'", "I'", "phips",
          "signgs"]


def run(cmd):
    p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, text=True)
    return p.returncode, p.stdout


def dyadic(x):
    """Exact (mantissa, exponent) of a finite double."""
    num, den = float(x).as_integer_ratio()
    e = 0
    while den > 1:
        den >>= 1
        e -= 1
    while num != 0 and num % 2 == 0:
        num //= 2
        e += 1
    return num, (e if num != 0 else 0)


def covering(wout, nodes, nu, gen_args, python, tmp, tag, surface=""):
    """Write one covering and return its path. `nodes` is the generator's
    node selection, `--node j` or `--nodes N`."""
    path = tmp / f"m_{tag}.txt"
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{path}" {nodes} '
                  f'--nu {nu}{surface} {gen_args}')
    if rc != 0:
        raise SystemExit(f"generator failed for {tag}:\n{out}")
    return path


def coverings(wout, nodes, nu, python, tmp, surface):
    return {
        "A": covering(wout, nodes, nu, "--cells --mercier a", python, tmp, "a",
                      surface),
        "B": covering(wout, nodes, nu, "--cells --mercier b", python, tmp, "b",
                      surface),
        "G": covering(wout, nodes, nu, "--radial --geometry", python, tmp, "g",
                      surface),
        "S": covering(wout, nodes, nu, "--radial --shear", python, tmp, "s",
                      surface),
    }


def run_file(path, node, covs, phip, signgs, filediff=None):
    lines = ["STELLAROCQ-MERCRUN", f"NODE {node}"]
    lines += [f"{k} {covs[k]}" for k in ("A", "B", "G", "S")]
    lines.append("PHIPS {} {}".format(*dyadic(phip)))
    lines.append("SIGNGS {} {}".format(*dyadic(signgs)))
    if filediff is not None:
        lines.append("FILEDIFF " + " ".join(f"{m} {e}" for m, e in filediff))
    path.write_text("\n".join(lines) + "\n")


def exact_dyadic(q):
    """A Fraction with a power-of-two denominator as (m, e), q = m 2^e."""
    from fractions import Fraction

    q = Fraction(q)
    den = q.denominator
    if den & (den - 1):
        raise SystemExit(f"{q} is not a dyadic number")
    m, e = q.numerator, -(den.bit_length() - 1)
    while m and m % 2 == 0:
        m //= 2
        e += 1
    return (m, e if m else 0)


def file_differences(d, j):
    """V'', p' in pascals, iota' and the current gradient at node j as the
    file's centred differences of its half-grid vp, pres, iotas and buco, each
    exact: (x[j + 1] - x[j]) / h with h = 1 / (ns - 1), V'' carrying signgs so
    that 4 pi^2 V'' is the angular integral of the radial derivative of the
    Jacobian."""
    from fractions import Fraction

    import numpy as np

    ns = int(d.variables["ns"][:])
    h = Fraction(1, ns - 1)
    sg = int(round(float(np.asarray(d.variables["signgs"][:]))))

    def diff(name, scale=1):
        x = np.asarray(d.variables[name][:], dtype=float)
        return exact_dyadic(scale * (Fraction(float(x[j + 1])) - Fraction(float(x[j]))) / h)

    return [diff("vp", sg), diff("pres"), diff("iotas"), diff("buco")]


def inputs_of(out):
    """The ten inputs a run printed, as (lo, hi) by name."""
    got = {}
    for name in INPUTS:
        m = re.search(r"^\s+" + re.escape(name) + r"\s+\[([0-9.e+-]+), "
                      r"([0-9.e+-]+)\]", out, re.M)
        if m:
            got[name] = (float(m.group(1)), float(m.group(2)))
    return got


def certified_nodes(cert):
    """The radius of each node block, from its own radii."""
    idx = []
    lines = pathlib.Path(cert).read_text().splitlines()
    for line in lines:
        if line.startswith("SNODES"):
            f = line.split()[1:]
            # the middle of the three is the node itself
            m, e = int(f[2]), int(f[3])
            idx.append(m * 2.0**e)
    return idx


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--node", type=int, default=None)
    ap.add_argument("--nu", type=int, default=512)
    ap.add_argument("--filediff", action="store_true",
                    help="take V'', p', iota' and the current gradient as the file's "
                         "centred differences (MercierFile.merc_run_q)")
    ap.add_argument(
        "--main",
        default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--write", default=None,
                    help="keep the run file")
    ap.add_argument("--profile", type=int, default=None, metavar="N",
                    help="every interior surface, N of them, in four "
                    "coverings rather than four per surface")
    ap.add_argument("--nv", type=int, default=None,
                    help="toroidal cells, which a three-dimensional "
                    "equilibrium needs: its integrals are over the whole "
                    "angular torus and a covering by curves is not one")
    a = ap.parse_args()

    import netCDF4
    import numpy as np

    with netCDF4.Dataset(a.wout) as _d:
        _d.set_auto_mask(False)
        _three_d = bool((np.asarray(_d.variables["xn"][:]) != 0).any())
    if _three_d and not a.nv:
        msg = ("this equilibrium is three-dimensional, so its surface "
               "integrals are over the whole torus: give --nv to cover it, "
               "since a covering by curves at sample toroidal angles is not "
               "a covering of the surface")
        raise SystemExit(msg)

    if a.node is None and a.profile is None:
        msg = "give --node for one surface or --profile N for all of them"
        raise SystemExit(msg)

    d = netCDF4.Dataset(a.wout)
    d.set_auto_mask(False)
    phip = float(np.asarray(d.variables["phips"][:])[1])
    signgs = float(np.asarray(d.variables["signgs"][:]))
    ns = int(d.variables["ns"][:])
    dmerc_file = (np.asarray(d.variables["DMerc"][:])
                  if "DMerc" in d.variables else None)
    have = ({k: float(np.asarray(d.variables[k][:])[a.node])
             for k in ("DMerc", "DShear", "DCurr", "DWell", "DGeod")
             if k in d.variables} if a.node is not None else {})
    fdiff = (file_differences(d, a.node)
             if a.node is not None and getattr(a, "filediff", False) else None)
    d.close()
    sf = f" --nv {a.nv} --surface" if a.nv else ""

    if a.profile is not None:
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="mercp_"))
        print(f"{a.wout}: the Mercier criterion over {a.profile} surfaces, "
              f"{a.nu} poloidal cells"
              + (f" by {a.nv} toroidal" if a.nv else ""))
        covs = coverings(a.wout, f"--nodes {a.profile}", a.nu, a.python, tmp, sf)
        radii = certified_nodes(covs["A"])
        print(f"\n{'s':>9} {'verdict':>9} {'margin':>13} {'file DMerc':>13} "
              f"{"V''":>9} {"I'":>9} {'averages':>10}")
        counts = {"UNSTABLE": 0, "STABLE": 0, "OPEN": 0}
        two_pi = 2.0 * 3.141592653589793
        pr = two_pi * phip * signgs
        for i, radius in enumerate(radii):
            path = tmp / f"merc_{i}.txt"
            run_file(path, i, covs, phip, signgs)
            rc, out = run(f'"{a.main}" --mercier-run "{path}"')
            ds = re.search(r"DStable\s+\[([0-9.e+-]+), ([0-9.e+-]+)\]", out)
            stable_mid = (0.5 * (float(ds.group(1)) + float(ds.group(2)))
                          if ds else float("nan"))
            mm = re.search(r"verdict: (\w+)\s+DMerc [<>]= ([0-9.e+-]+)", out)
            if mm:
                verdict, margin = mm.group(1), float(mm.group(2))
            else:
                verdict, margin = "OPEN", float("nan")
            counts[verdict] = counts.get(verdict, 0) + 1
            j = int(round(radius * (ns - 1)))
            fv = (dmerc_file[j] if dmerc_file is not None and j < len(dmerc_file)
                  else float("nan"))
            vals = inputs_of(out)
            if len(vals) < len(INPUTS):
                print(f"{radius:>9.5f} {verdict:>9}   (no inputs: "
                      f"{out.strip().splitlines()[-1] if out.strip() else rc})")
                continue
            # What a relative error in one input does to the criterion.
            # Every term is a difference of larger numbers, so a change of
            # one part in a hundred somewhere can be a change of the whole
            # answer. These are the factors: a one per cent error in the
            # input moves the criterion by that many per cent of itself, and
            # anything large means the number is set by how a quantity was
            # defined rather than by the equilibrium.
            mid = lambda iv: 0.5 * (iv[0] + iv[1])  # noqa: E731
            fp2 = 4.0 * 3.141592653589793**2
            ip_ = signgs * mid(vals["I'"]) / (two_pi * pr)
            presp = mid(vals["mu0 p'"]) / (fp2 * pr)
            vpp = mid(vals["V''"]) / (pr * pr)
            shear = mid(vals["iota'"]) / (fp2 * pr)
            base = abs(stable_mid)

            def amp(x):
                return abs(x) / base if base > 0 else float("inf")

            a_vpp = amp(presp * mid(vals["tbb"]) * vpp)
            a_ip = amp(shear * ip_ * mid(vals["tbb"]))
            a_avg = amp(mid(vals["tjb"]) ** 2)
            print(f"{radius:>9.5f} {verdict:>9} {margin:>13.6e} "
                  f"{fv:>13.6e} {a_vpp:>9.1f} {a_ip:>9.1f} "
                  f"{a_avg:>10.3g}")
        print(f"\n{counts.get('UNSTABLE', 0)} surfaces proven unstable, "
              f"{counts.get('STABLE', 0)} proven stable, "
              f"{counts.get('OPEN', 0)} undecided by this covering")
        print("The last three columns are what a relative error in one input "
              "does to the\ncriterion: a one per cent error in V'', in the "
              "current gradient, or in the\nsurface averages moves it by that "
              "many per cent of itself. Where a factor is\nlarge the number "
              "is set by how the quantity was defined rather than by the\n"
              "equilibrium, which is why the averages need an inequality "
              "rather than an\nenclosure.")
        return 0

    tmp = pathlib.Path(tempfile.mkdtemp(prefix="merc_"))
    print(f"{a.wout} node {a.node}, {a.nu} poloidal cells"
          + (f" by {a.nv} toroidal" if a.nv else ""))
    covs = coverings(a.wout, f"--node {a.node}", a.nu, a.python, tmp, sf)
    path = pathlib.Path(a.write) if a.write else tmp / "merc.txt"
    run_file(path, 0, covs, phip, signgs, fdiff)
    print()
    rc, out = run(f'"{a.main}" --mercier-run "{path}"')
    print(out.strip())
    if have:
        print("\nthe file's own numbers at this surface:")
        for k, v in have.items():
            print(f"  {k:<7} {v:+.6e}")
    print(f"\nthe run file is {path}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
