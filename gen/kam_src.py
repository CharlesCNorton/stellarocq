"""Write the integer data of the check of the sources (KSrcRun.srcdata).

    python gen/kam_src.py e0_full2.dat OUT [--kr 8 80] [--ky 8 70] [--N1s 65 --N2s 605]

The torus rows, the seeds Ub and gs, the sources, the rotation number and the
crude claims are those of the data of the check of the first torus. The seed of
each source is q^(-1/2) along the reference torus (the first torus with every
mode outside |k| <= kr1, |n| <= kr2 cleared) truncated to |k| <= ky1,
|n| <= ky2, in (cosine, sine) mantissas at scale 2^-sY over every toroidal mode.
"""
import argparse
import time

import mpmath as mp
import numpy as np

KFX = 192
KAPPA = 0.1
mp.mp.dps = 120

ap = argparse.ArgumentParser()
ap.add_argument("e0data")
ap.add_argument("out")
ap.add_argument("--kr", type=int, nargs=2, default=[8, 80])
ap.add_argument("--ky", type=int, nargs=2, default=[8, 70])
ap.add_argument("--N1s", type=int, default=65)
ap.add_argument("--N2s", type=int, default=605)
ap.add_argument("--sY", type=int, default=80)
ap.add_argument("--nt", type=int, default=128)
ap.add_argument("--nf", type=int, default=1024)
ap.add_argument("--w0", default="1/20")
ap.add_argument("--w1", default="3/10")
ap.add_argument("--nsrc", type=int, default=0)
a = ap.parse_args()
t0 = time.time()

toks = open(a.e0data).read().split()
pos = 0


def nxt():
    global pos
    pos += 1
    return toks[pos - 1]


P, N1, M, K1, K2, D, Km, Kn, Kmu, Knu, Kmg, Kng = (int(nxt()) for _ in range(12))
s0 = int(nxt())


def rows(ka, kb):
    return [[int(nxt()) for _ in range(2 * kb + 1)] for _ in range(2 * ka + 1)]


rowsR, rowsZ, rowsU, rowsG = rows(Km, Kn), rows(Km, Kn), rows(Kmu, Knu), rows(Kmg, Kng)
ssrc = int(nxt())
ns = int(nxt())
srcs = [[int(nxt()) for _ in range(6)] for _ in range(ns)]
aa, bb = int(nxt()), int(nxt())
trig_e0 = [(int(nxt()), int(nxt())) for _ in range(6)]
exp_e0 = [(int(nxt()), int(nxt())) for _ in range(7)]
bounds_e0 = [(int(nxt()), int(nxt())) for _ in range(8)]
assert pos == len(toks)
if a.nsrc:
    srcs = srcs[:a.nsrc]
    ns = a.nsrc


def zrange(K):
    out = []
    for j in range(K, 0, -1):
        out += [j, -j]
    return out + [0]


kr1, kr2 = a.kr
ky1, ky2 = a.ky
# the reference torus on the seed grid (whole torus), from the mantissas
Nt, Nf = a.nt, a.nf
th = 2 * np.pi * np.arange(Nt) / Nt
ph = 2 * np.pi * np.arange(Nf) / Nf
R = np.zeros((Nt, Nf))
Z = np.zeros((Nt, Nf))
for i, k in enumerate(zrange(Km)):
    if abs(k) > kr1:
        continue
    for j, l in enumerate(zrange(Kn)):
        n = P * l
        if abs(n) > kr2:
            continue
        ang = k * th[:, None] + n * ph[None, :]
        R += rowsR[i][j] / 2.0 ** s0 * np.cos(ang)
        Z += rowsZ[i][j] / 2.0 ** s0 * np.sin(ang)
X = np.stack([R * np.cos(ph)[None, :], R * np.sin(ph)[None, :], Z], -1)
print(f"reference torus on {Nt} x {Nf} ({time.time() - t0:.0f} s)", flush=True)

kt = np.fft.fftfreq(Nt, 1.0 / Nt).astype(int)
nt = np.fft.fftfreq(Nf, 1.0 / Nf).astype(int)
seeds = []
for j in range(ns):
    p = np.array(srcs[j][:3], dtype=float) / 2.0 ** ssrc
    r = X - p[None, None, :]
    y = np.sum(r * r, -1) ** -0.5
    F = np.fft.fft2(y) / y.size
    rows_j = []
    for k in zrange(ky1):
        rows_j.append([(int(round(F[k % Nt, n % Nf].real * 2.0 ** a.sY)), int(round(-F[k % Nt, n % Nf].imag * 2.0 ** a.sY)))
                       for n in zrange(ky2)])
    seeds.append(rows_j)
print(f"{ns} seeds ({time.time() - t0:.0f} s)", flush=True)


def encl(x):
    y = x * mp.mpf(2) ** KFX
    return int(mp.floor(y)) - 1, int(mp.ceil(y)) + 1


w0 = mp.mpf(mp.fraction(*map(int, a.w0.split("/"))))
w1 = mp.mpf(mp.fraction(*map(int, a.w1.split("/"))))
kap = mp.mpf(1) / 10
trig = []
for Nn in (a.N1s, a.N2s):
    trig += [encl(mp.cos(2 * mp.pi / Nn)), encl(mp.sin(2 * mp.pi / Nn))]
exps = []
for w in (w0, w1):
    exps += [encl(mp.exp(w)), encl(mp.exp(w * kap)), encl(mp.exp(w * kap * P))]
with open(a.out, "w") as f:
    f.write(f"{P} {Km} {Kn} {kr1} {kr2} {a.N1s} {a.N2s} {ky1} {ky2} {Kmu} {Knu} {Kmg} {Kng}\n{s0} {a.sY} {ssrc}\n")
    for R_ in (rowsR, rowsZ, rowsU, rowsG):
        for row in R_:
            f.write(" ".join(map(str, row)) + "\n")
    f.write(f"{ns}\n")
    for s in srcs:
        f.write(" ".join(map(str, s)) + "\n")
    for rows_j in seeds:
        for row in rows_j:
            f.write(" ".join(f"{c} {s}" for c, s in row) + "\n")
    f.write(f"{aa} {bb}\n")
    for lo, hi in trig + exps + bounds_e0[:4]:
        f.write(f"{lo} {hi}\n")
print(f"wrote {a.out}: {ns} sources, seeds {ky1} x {ky2}, reference box {kr1} x {kr2}, grid {a.N1s} x {a.N2s} "
      f"({time.time() - t0:.0f} s)")
