"""Where the free-boundary jump of the CTH-like case lies in Fourier space.

VMEC++ imposes the free-boundary balance through the Fourier harmonics it
retains. Each run here solves the CTH-like free-boundary case of the VMEC++
test data at one radial resolution ns, one angular resolution (mpol, ntor) and
one NESTOR grid (ntheta, nzeta), with `return_vacuum_field` set, and reports in
floating point the largest jump |p + B^2/2 - B_vac^2/2| on NESTOR's grid, the
quantity gen/free_boundary.py certifies, together with the largest value of
its part in the retained harmonics (m < mpol, |n| <= ntor, n in units of nfp)
and of its part beyond them, by a discrete Fourier transform over one field
period, and the harmonics that carry the most of it.

  python gen/fb_harmonics.py 25,5,4,0,36 49,5,4,0,36 97,5,4,0,36
  python gen/fb_harmonics.py 49,7,4,32,36 49,12,4,32,36 --out DIR

Each argument is ns,mpol,ntor,ntheta,nzeta; ntheta 0 is VMEC++'s default for
the mpol given, and nzeta is held to the mgrid's 36 planes. `--out` keeps each
run's wout and NESTOR boundary field.
"""

import argparse
import pathlib
import sys
import time

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from vacuum_answers import cth_input, full_theta  # noqa: E402


def pad(a, shape):
    """a centred in toroidal index inside zeros of the given shape."""
    a = np.asarray(a, dtype=float)
    out = np.zeros(shape)
    m0, n0 = a.shape
    nt_old, nt_new = (n0 - 1) // 2, (shape[1] - 1) // 2
    mm = min(m0, shape[0])
    for n in range(-min(nt_old, nt_new), min(nt_old, nt_new) + 1):
        out[:mm, n + nt_new] = a[:mm, n + nt_old]
    return out


def config(ns, mpol, ntor, ntheta, nzeta):
    vi, _ = cth_input(ns)
    if (mpol, ntor) != (vi.mpol, vi.ntor):
        shape = (mpol, 2 * ntor + 1)
        rc = np.zeros(ntor + 1)
        zs = np.zeros(ntor + 1)
        k = min(ntor, vi.ntor) + 1
        rc[:k] = np.asarray(vi.raxis_c)[:k]
        zs[:k] = np.asarray(vi.zaxis_s)[:k]
        vi = vi.model_copy(update={"mpol": mpol, "ntor": ntor,
                                   "rbc": pad(vi.rbc, shape), "zbs": pad(vi.zbs, shape),
                                   "raxis_c": rc, "zaxis_s": zs}, deep=True)
    return vi.model_copy(update={"ntheta": ntheta, "nzeta": nzeta}, deep=True)


def split(J, mpol, ntor):
    """The largest values of J's parts in and beyond the retained harmonics,
    and J's largest harmonics as (m, n, amplitude)."""
    nz, nth = J.shape
    F = np.fft.fft2(J) / J.size
    kz = np.fft.fftfreq(nz, 1.0 / nz)
    kt = np.fft.fftfreq(nth, 1.0 / nth)
    KZ, KT = np.meshgrid(kz, kt, indexing="ij")
    keep = (np.abs(KT) < mpol) & (np.abs(KZ) <= ntor)
    inside = np.real(np.fft.ifft2(np.where(keep, F, 0) * J.size))
    amp = np.abs(F)
    top = []
    for idx in np.argsort(amp, axis=None)[::-1]:
        a, b = np.unravel_index(idx, amp.shape)
        m, n = int(KT[a, b]), int(-KZ[a, b])
        # a real J carries each harmonic twice, at (m, n) and (-m, -n)
        if m < 0 or (m == 0 and n < 0):
            continue
        top.append((m, n, 2 * amp[a, b]))
        if len(top) == 4:
            break
    return np.abs(inside).max(), np.abs(J - inside).max(), top


def run(ns, mpol, ntor, ntheta, nzeta, out_dir):
    import vmecpp

    tag = f"ns{ns}_m{mpol}n{ntor}_t{ntheta}z{nzeta}"
    t0 = time.time()
    out = vmecpp.run(config(ns, mpol, ntor, ntheta, nzeta), verbose=False)
    fb = out.threed1_free_boundary
    nh = np.asarray(fb.bsqvacf).shape[1]
    nth = 2 * (nh - 1)
    J = full_theta(np.asarray(fb.bsqmhdf), nth) - full_theta(np.asarray(fb.bsqvacf), nth)
    ins, outs, top = split(J, mpol, ntor)
    w = out.wout
    print(f"{tag}: grid {J.shape[0]}x{nth}, fsq {w.fsqr:.1e} {w.fsqz:.1e} {w.fsql:.1e}, "
          f"max|jump| {np.abs(J).max():.5e}, in the retained harmonics {ins:.3e}, "
          f"beyond {outs:.3e}; largest "
          + ", ".join(f"({m},{n}) {a:.2e}" for m, n, a in top)
          + f"; {time.time() - t0:.0f} s", flush=True)
    if out_dir is not None:
        w.save(str(out_dir / f"wout_cth_{tag}.nc"))
        np.savez(out_dir / f"fb_cth_{tag}.npz", **{k: np.asarray(getattr(fb, k)) for k in
                 ("rb", "zb", "phib", "bsqmhdf", "bsqvacf", "brv", "bphiv", "bzv",
                  "bredge", "bpedge", "bzedge")})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("runs", nargs="+", help="ns,mpol,ntor,ntheta,nzeta")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    out_dir = None
    if a.out is not None:
        out_dir = pathlib.Path(a.out)
        out_dir.mkdir(parents=True, exist_ok=True)
    for spec in a.runs:
        run(*(int(x) for x in spec.split(",")), out_dir)


if __name__ == "__main__":
    main()
