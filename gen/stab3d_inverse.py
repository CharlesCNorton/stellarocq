"""The frame exponents and the approximate inverse R of the three-dimensional
stability check's assembly (Final3d.assemble3d).

    python gen/stab3d_inverse.py FRAMES CELLDIR START OUT_ES OUT_R

Reads the frames, the ranges the cell stage recorded in CELLDIR and those of
the start rows, and mirrors assemble3d in binary64: the reference steps
G = I + 2^-16 mid of each step's range, their products P_k over the
segments, the reference system M0 of the rescaled frames 2^e_k W_k, and the
bound rho on the rows of every level's system less M0. The exponents e_k
minimize th1 = max_i sum_j |R_ij| rho_j with R = M0^-1 by coordinate
descent. The checker encloses everything from R itself, and no number here is
trusted.

The paper's certificate, with the checker of `make c3`
(C = colloc3d/_ext/_build/default/main.exe) and the frames of
gen/stab3d_frames.py:

  mkdir run
  C start colloc3d/cert/frames3d.txt run/start.txt
  C cells2 colloc3d/cert/frames3d.txt run 16 0 14 13
  python gen/stab3d_inverse.py colloc3d/cert/frames3d.txt run run/start.txt \\
      colloc3d/cert/es3d.txt colloc3d/cert/r3d.txt
  C assemble colloc3d/cert/frames3d.txt colloc3d/cert/es3d.txt run run/start.txt \\
      colloc3d/cert/r3d.txt
  C ball 23 -20 -20 -16 16
  C cons2 13 -16 16

`cells2` records each cell's ranges with |M^-1| <= 2^0, |M| <= 2^14 and
|Q| <= 2^13 checked (CellTM.cell_ranges2), and `cells` the same ranges
without them. The assembly prints `assemble3d: true`, the hypothesis of
Final3d.assemble3d_sound and of Lin3d's and Stab3d's theorems, whose other
hypotheses are the cell and start ranges the first two compute. `ball` prints
`ball verdict over 1728 checks: true`, Ball3d.ball_cell_ok of every point over
every cell with the bound 2^23, the radii 2^-20 and the steps h <= 2^-16, and
`cons2` prints `consistency verdict over 1728 checks: true`,
ConsCheck.cons2_cell_ok of every point over every cell with the bound 2^13 on
the second derivative in h for |h| <= 2^-16. Together they are the
hypotheses of Consist3d.colloc3d_convergent.
"""
import glob
import math
import pathlib
import sys

import numpy as np

HR = 2.0 ** -16
NSUB = 16
NSTEP = 256 * NSUB


def read_frames(path):
    rows = [[float.fromhex(x) for x in line.split()] for line in open(path)]
    out = []
    for k in range(12):
        W = np.array(rows[28 * k: 28 * k + 14])
        D = np.array(rows[28 * k + 14: 28 * k + 28])
        out.append((W, D))
    return out


def read_cells(celldir):
    steps = {}
    for name in glob.glob(str(pathlib.Path(celldir) / "cells_*.txt")):
        for line in open(name):
            f = line.split()
            if len(f) != 2 + NSUB * 392:
                continue
            k, j = int(f[0]), int(f[1])
            v = np.array([float.fromhex(x) for x in f[2:]]).reshape(NSUB, 14, 14, 2)
            for q in range(NSUB):
                steps[(k, NSUB * j + q)] = (v[q, :, :, 0], v[q, :, :, 1])
    return steps


def read_start(path):
    f = open(path).read().split()
    v = np.array([float.fromhex(x) for x in f]).reshape(5, 14, 2)
    return v[:, :, 0], v[:, :, 1]


def step_consts(lo, hi):
    mid = 0.5 * (lo + hi)
    rad = np.maximum(np.abs(lo - mid), np.abs(hi - mid))
    om = rad.sum(axis=1).max()
    nu = np.maximum(np.abs(lo), np.abs(hi)).sum(axis=1).max()
    G = np.eye(14) + HR * mid
    q = np.abs(G).sum(axis=1).max()
    l = HR * om + math.expm1(HR * nu) - HR * nu
    return G, q, l


def segment(steps_k):
    """The product of a segment's reference steps and its delta,
    prod (q + l) - prod q."""
    P = np.eye(14)
    A = 1.0
    B = 1.0
    for lo, hi in steps_k:
        G, q, l = step_consts(lo, hi)
        P = G @ P
        A *= q + l
        B *= q
    return P, A - B


def system(frames, es, Ps, deltas, slo, shi):
    Ws = [2.0 ** e * W for (W, _), e in zip(frames, es)]
    Wis = [2.0 ** -e * D for (_, D), e in zip(frames, es)]
    N = 14 * 13
    M0 = np.zeros((N, N))
    rho = np.zeros(N)
    s = 2.0 ** -es[0]
    lo, hi = s * slo, s * shi
    smid = 0.5 * (lo + hi)
    M0[0:5, 0:14] = smid
    rho[0:5] = np.maximum(np.abs(lo - smid), np.abs(hi - smid)).sum(axis=1)
    for r in range(5, 14):
        M0[r, 14 * 12 + r] = 1.0
    for I in range(1, 12):
        T = Ws[I] @ Wis[I - 1]
        M0[14 * I:14 * I + 14, 14 * (I - 1):14 * I] = -T @ Ps[I - 1]
        M0[14 * I:14 * I + 14, 14 * I:14 * I + 14] = np.eye(14)
        rho[14 * I:14 * I + 14] = np.abs(T).sum(axis=1) * deltas[I - 1]
    M0[14 * 12:, 14 * 11:14 * 12] = Ps[11]
    E0p = np.zeros((14, 14))
    for c in range(5):
        E0p[9 + c, c] = 1.0
    M0[14 * 12:, 14 * 12:] = -Ws[11] @ E0p
    rho[14 * 12:] = deltas[11]
    R = np.linalg.inv(M0)
    th1 = (np.abs(R) @ rho).max()
    th0 = np.abs(np.eye(N) - R @ M0).sum(axis=1).max()
    return R, th0, th1, np.abs(R).sum(axis=1).max()


def main():
    ffile, celldir, sfile, out_es, out_r = sys.argv[1:6]
    frames = read_frames(ffile)
    steps = read_cells(celldir)
    print(f"{len(steps)} reference steps read", flush=True)
    Ps, deltas = [], []
    for k in range(12):
        missing = [i for i in range(NSTEP) if (k, i) not in steps]
        if missing:
            sys.exit(f"segment {k}: {len(missing)} steps missing")
        P, dl = segment([steps[(k, i)] for i in range(NSTEP)])
        Ps.append(P)
        deltas.append(dl)
        print(f"segment {k}: delta {dl:.4e}  |P| {np.abs(P).sum(axis=1).max():.4e}", flush=True)
    slo, shi = read_start(sfile)
    es = [0] * 12
    best = system(frames, es, Ps, deltas, slo, shi)
    print(f"e = 0: th0 {best[1]:.3e}  th1 {best[2]:.4f}  |R| {best[3]:.3e}", flush=True)
    improved = True
    while improved:
        improved = False
        for k in range(12):
            for step in (1, -1):
                trial = list(es)
                trial[k] += step
                res = system(frames, trial, Ps, deltas, slo, shi)
                if res[2] < best[2] * 0.999:
                    es, best, improved = trial, res, True
    print(f"e = {es}: th0 {best[1]:.3e}  th1 {best[2]:.4f}  |R| {best[3]:.3e}", flush=True)
    open(out_es, "w").write(" ".join(str(e) for e in es) + "\n")
    with open(out_r, "w") as f:
        for row in best[0]:
            f.write(" ".join(float(x).hex() for x in row) + "\n")


if __name__ == "__main__":
    main()
