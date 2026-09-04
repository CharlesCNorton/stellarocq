"""The Mercier criterion of one surface, end to end from a wout.

Four coverings supply the ten numbers `mercier.f90` combines:

  --mercier a           tpp, tbb, tjb      angular integrals over the torus
  --mercier b           tjj
  --radial --geometry   dV/ds, V''         off the free-radius reconstruction
  --radial --shear      iota', dB_u/ds, mu0 p'

and phips and signgs come from the wout. This runs all four, collects the
enclosures the checker printed, writes them as exact dyadic endpoints, and
hands them to `main --mercier`, which assembles DShear, DCurr, DWell, DGeod
and DMerc inside the extracted code. Nothing between the certified integrals
and the verdict happens in floating point here: the endpoints are transferred
in hexadecimal, which round-trips exactly, and every arithmetic step is the
interval arithmetic theories/Mercier.v reasons about.

  python gen/mercier.py wout.nc --node 22 [--nu 512] [--main PATH]

`--write FILE` keeps the assembled input, which is what another party would
re-check.

`--profile` does every interior surface at once. The four coverings each carry
every node, so a whole profile costs four runs rather than four per surface,
and what comes out is the criterion as a function of the radius: where it is
negative, by how much, and where the covering cannot decide.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
GEN = ROOT / "gen" / "make_cert.py"

# the slot order theories/Mercier.v fixes
TAGS = ["TPP", "TBB", "TJB", "TJJ", "VPP", "PP", "IOTAP", "IPINT", "PHIP",
        "SIGNGS"]


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


def integrals_profile(wout, nodes, nu, gen_args, labels, main, python, tmp,
                      tag, surface=""):
    """The same, over every node of one covering.

    A certificate carries as many node blocks as it likes and the checker
    reports an integral per node, so a profile is four runs rather than four
    per surface.
    """
    src = tmp / f"p_{tag}.txt"
    dst = tmp / f"p_{tag}_c.txt"
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" --nodes {nodes} '
                  f'--nu {nu}{surface} {gen_args}')
    if rc != 0:
        raise SystemExit(f"generator failed for {tag}:\n{out}")
    rc, out = run(f'"{main}" --tighten "{src}" "{dst}"')
    if rc != 0:
        raise SystemExit(f"tighten failed for {tag}:\n{out}")
    rc, out = run(f'"{main}" --integrate "{dst}"')
    if rc != 0:
        raise SystemExit(f"integrate failed for {tag}:\n{out}")
    # the driver prints one block per node, in the order the file carries them
    blocks = re.split(r"^  node (\d+):", out, flags=re.M)
    got = []
    for i in range(1, len(blocks) - 1, 2):
        body = blocks[i + 1]
        one = {}
        for label in labels:
            m = re.search(r"^\s+" + re.escape(label) + r"\s+exact\s+(\S+)"
                          r"\s+(\S+)", body, re.M)
            if not m:
                raise SystemExit(f"no exact endpoints for {label} in a node "
                                 f"block of {tag}")
            one[label] = (float.fromhex(m.group(1)), float.fromhex(m.group(2)))
        got.append(one)
    return got, src


def certified_nodes(cert):
    """The wout node index of each node block, from its own radii."""
    idx = []
    lines = pathlib.Path(cert).read_text().splitlines()
    for i, line in enumerate(lines):
        if line.startswith("SNODES"):
            f = line.split()[1:]
            # the middle of the three is the node itself
            m, e = int(f[2]), int(f[3])
            idx.append(m * 2.0**e)
    return idx


def integrals(wout, node, nu, gen_args, labels, main, python, tmp, tag,
              surface=""):
    """Run one covering and return the exact endpoints of each labelled
    integral, as a dict from label to (lo, hi)."""
    src = tmp / f"m_{tag}.txt"
    dst = tmp / f"m_{tag}_c.txt"
    rc, out = run(f'"{python}" "{GEN}" "{wout}" "{src}" --node {node} '
                  f'--nu {nu}{surface} {gen_args}')
    if rc != 0:
        raise SystemExit(f"generator failed for {tag}:\n{out}")
    rc, out = run(f'"{main}" --tighten "{src}" "{dst}"')
    if rc != 0:
        raise SystemExit(f"tighten failed for {tag}:\n{out}")
    rc, out = run(f'"{main}" --integrate "{dst}"')
    if rc != 0:
        raise SystemExit(f"integrate failed for {tag}:\n{out}")
    got = {}
    for label in labels:
        # the exact line the driver prints beside the decimal one
        m = re.search(r"^\s+" + re.escape(label) + r"\s+exact\s+(\S+)"
                      r"\s+(\S+)", out, re.M)
        if not m:
            raise SystemExit(f"no exact endpoints for {label} in:\n{out}")
        got[label] = (float.fromhex(m.group(1)), float.fromhex(m.group(2)))
    return got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("wout")
    ap.add_argument("--node", type=int, default=None)
    ap.add_argument("--nu", type=int, default=512)
    ap.add_argument(
        "--main",
        default=str(ROOT / "extract" / "_build" / "default" / "main.exe"))
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("--write", default=None,
                    help="keep the assembled input file")
    ap.add_argument("--prec", type=int, default=53)
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
    d.close()

    if a.profile is not None:
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="mercp_"))
        print(f"{a.wout}: the Mercier criterion over {a.profile} surfaces, "
              f"{a.nu} poloidal cells"
              + (f" by {a.nv} toroidal" if a.nv else ""))
        sf = f" --nv {a.nv} --surface" if a.nv else ""
        ma, src = integrals_profile(a.wout, a.profile, a.nu,
                                    "--cells --mercier a",
                                    ["tpp", "tbb", "tjb"], a.main, a.python,
                                    tmp, "a", sf)
        mb, _ = integrals_profile(a.wout, a.profile, a.nu,
                                  "--cells --mercier b", ["tjj"], a.main,
                                  a.python, tmp, "b", sf)
        mg, _ = integrals_profile(a.wout, a.profile, a.nu,
                                  "--radial --geometry", ["dV/ds", "V''"],
                                  a.main, a.python, tmp, "g", sf)
        ms, _ = integrals_profile(a.wout, a.profile, a.nu,
                                  "--radial --shear",
                                  ["iota'", "dB_u/ds", "mu0 p'"], a.main,
                                  a.python, tmp, "s", sf)
        radii = certified_nodes(src)
        n = min(len(ma), len(mb), len(mg), len(ms), len(radii))
        print(f"\n{'s':>9} {'verdict':>9} {'margin':>13} {'file DMerc':>13} "
              f"{"V''":>9} {"I'":>9} {'averages':>10}")
        counts = {"UNSTABLE": 0, "STABLE": 0, "OPEN": 0}
        two_pi = 2.0 * 3.141592653589793
        pr = two_pi * phip * signgs
        for i in range(n):
            vals = {
                "TPP": ma[i]["tpp"], "TBB": ma[i]["tbb"], "TJB": ma[i]["tjb"],
                "TJJ": mb[i]["tjj"], "VPP": mg[i]["V''"],
                "PP": ms[i]["mu0 p'"], "IOTAP": ms[i]["iota'"],
                "IPINT": ms[i]["dB_u/ds"],
                "PHIP": (phip, phip), "SIGNGS": (signgs, signgs),
            }
            lines = ["STELLAROCQ-MERC 1", f"PREC {a.prec}"]
            for t in TAGS:
                lo, hi = vals[t]
                mlo, elo = dyadic(lo)
                mhi, ehi = dyadic(hi)
                lines.append(f"{t} {mlo} {elo} {mhi} {ehi}")
            path = tmp / f"merc_{i}.txt"
            path.write_text("\n".join(lines) + "\n")
            rc, out = run(f'"{a.main}" --mercier "{path}"')
            ds = re.search(r"DStable\s+\[([0-9.e+-]+), ([0-9.e+-]+)\]", out)
            stable_mid = (0.5 * (float(ds.group(1)) + float(ds.group(2)))
                          if ds else float("nan"))
            mm = re.search(r"verdict: (\w+)\s+DMerc [<>]= ([0-9.e+-]+)", out)
            if mm:
                verdict, margin = mm.group(1), float(mm.group(2))
            else:
                verdict, margin = "OPEN", float("nan")
            counts[verdict] = counts.get(verdict, 0) + 1
            j = int(round(radii[i] * (ns - 1)))
            fv = (dmerc_file[j] if dmerc_file is not None and j < len(dmerc_file)
                  else float("nan"))
            # What a relative error in one input does to the criterion.
            # Every term is a difference of larger numbers, so a change of
            # one part in a hundred somewhere can be a change of the whole
            # answer. These are the factors: a one per cent error in the
            # input moves the criterion by that many per cent of itself, and
            # anything large means the number is set by how a quantity was
            # defined rather than by the equilibrium.
            mid = lambda iv: 0.5 * (iv[0] + iv[1])  # noqa: E731
            fp2 = 4.0 * 3.141592653589793**2
            ip_ = signgs * mid(vals["IPINT"]) / (two_pi * pr)
            presp = mid(vals["PP"]) / (fp2 * pr)
            vpp = mid(vals["VPP"]) / (pr * pr)
            shear = mid(vals["IOTAP"]) / (fp2 * pr)
            base = abs(stable_mid)

            def amp(x):
                return abs(x) / base if base > 0 else float("inf")

            a_vpp = amp(presp * mid(vals["TBB"]) * vpp)
            a_ip = amp(shear * ip_ * mid(vals["TBB"]))
            a_avg = amp(mid(vals["TJB"]) ** 2)
            print(f"{radii[i]:>9.5f} {verdict:>9} {margin:>13.6e} "
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
    sf = f" --nv {a.nv} --surface" if a.nv else ""
    print(f"{a.wout} node {a.node}, {a.nu} poloidal cells"
          + (f" by {a.nv} toroidal" if a.nv else ""))
    ma = integrals(a.wout, a.node, a.nu, "--cells --mercier a",
                   ["tpp", "tbb", "tjb"], a.main, a.python, tmp, "a", sf)
    mb = integrals(a.wout, a.node, a.nu, "--cells --mercier b",
                   ["tjj"], a.main, a.python, tmp, "b", sf)
    mg = integrals(a.wout, a.node, a.nu, "--radial --geometry",
                   ["dV/ds", "V''"], a.main, a.python, tmp, "g", sf)
    ms = integrals(a.wout, a.node, a.nu, "--radial --shear",
                   ["iota'", "dB_u/ds", "mu0 p'"], a.main, a.python, tmp, "s",
                   sf)

    vals = {
        "TPP": ma["tpp"], "TBB": ma["tbb"], "TJB": ma["tjb"], "TJJ": mb["tjj"],
        "VPP": mg["V''"], "PP": ms["mu0 p'"], "IOTAP": ms["iota'"],
        "IPINT": ms["dB_u/ds"],
        "PHIP": (phip, phip), "SIGNGS": (signgs, signgs),
    }

    lines = ["STELLAROCQ-MERC 1", f"PREC {a.prec}"]
    for t in TAGS:
        lo, hi = vals[t]
        mlo, elo = dyadic(lo)
        mhi, ehi = dyadic(hi)
        lines.append(f"{t} {mlo} {elo} {mhi} {ehi}")
    text = "\n".join(lines) + "\n"
    path = pathlib.Path(a.write) if a.write else tmp / "merc.txt"
    path.write_text(text)

    print("\ncertified inputs, exactly as the coverings left them:")
    for t in TAGS:
        lo, hi = vals[t]
        print(f"  {t:<7} [{lo:+.9e}, {hi:+.9e}]")
    print()
    rc, out = run(f'"{a.main}" --mercier "{path}"')
    print(out.strip())
    if have:
        print("\nthe file's own numbers at this surface:")
        for k, v in have.items():
            print(f"  {k:<7} {v:+.6e}")
    print(f"\nthe assembled input is {path}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
