"""Write the integer data of the check of the jet (KJets.jetsdata).

    python gen/kam_jets.py e0_full2.dat OUT --N1 280 --M 560 --K1 130 --K2 260 --D 1303 [--kj 12 36]

The torus and the sources are those of the data of the check of the first torus.
The finite approximants of the nine components of the jet of the field along the
torus (B_R, B_phi, B_Z and their R and Z derivatives) are the truncated transforms
of their values on a grid of one period, in sine or cosine mantissas by parity at
scale 2^-sJ; the claims are the crude norms on the wide strip plus the norms of
the approximants there, times a margin, and a bound for each difference.
"""
import argparse
import time

import mpmath as mp
import numpy as np

KFX = 192
NFP = 5
KAPPA = 0.1
mp.mp.dps = 120

ap = argparse.ArgumentParser()
ap.add_argument("e0data")
ap.add_argument("out")
ap.add_argument("--N1", type=int, required=True)
ap.add_argument("--M", type=int, required=True)
ap.add_argument("--K1", type=int, required=True)
ap.add_argument("--K2", type=int, required=True)
ap.add_argument("--D", type=int, required=True)
ap.add_argument("--kj", type=int, nargs=2, default=[12, 36])
ap.add_argument("--sJ", type=int, default=80)
ap.add_argument("--nt", type=int, default=128)
ap.add_argument("--nf", type=int, default=256)
ap.add_argument("--w", default="1/20")
ap.add_argument("--wc", default="3/10")
ap.add_argument("--crude", type=float, nargs=9,
                default=[7.634e3, 7.634e3, 4.867e3, 2.651e6, 1.800e5, 2.651e6, 1.800e5, 1.774e6, 1.240e5])
ap.add_argument("--margin", type=float, default=3.0)
ap.add_argument("--B", type=float, default=3e-6)
a = ap.parse_args()
t0 = time.time()

toks = open(a.e0data).read().split()
pos = 0


def nxt():
    global pos
    pos += 1
    return toks[pos - 1]


P, _, _, _, _, _, Km, Kn, Kmu, Knu, Kmg, Kng = (int(nxt()) for _ in range(12))
s0 = int(nxt())


def rows(ka, kb):
    return [[int(nxt()) for _ in range(2 * kb + 1)] for _ in range(2 * ka + 1)]


rowsR, rowsZ, _, _ = rows(Km, Kn), rows(Km, Kn), rows(Kmu, Knu), rows(Kmg, Kng)
ssrc = int(nxt())
ns = int(nxt())
srcs = [[int(nxt()) for _ in range(6)] for _ in range(ns)]


def zrange(K):
    out = []
    for j in range(K, 0, -1):
        out += [j, -j]
    return out + [0]


w = float(mp.fraction(*map(int, a.w.split("/"))))
wc = float(mp.fraction(*map(int, a.wc.split("/"))))
Nt, Nf = a.nt, a.nf
th = 2 * np.pi * np.arange(Nt) / Nt
ph = (2 * np.pi / NFP) * np.arange(Nf) / Nf
ks_, ls_ = np.array(zrange(Km)), np.array(zrange(Kn))
CR = np.array(rowsR, dtype=float) / 2.0 ** s0
SZ = np.array(rowsZ, dtype=float) / 2.0 ** s0
Et = np.exp(1j * np.outer(th, ks_))
Ep = np.exp(1j * np.outer(NFP * ls_, ph))
R = np.real(Et @ CR.astype(complex) @ Ep)
Z = np.real(Et @ (-1j * SZ) @ Ep)
Pb = np.array([s[:3] for s in srcs], dtype=float) / 2.0 ** ssrc
Db = np.array([s[3:] for s in srcs], dtype=float) / 2.0 ** ssrc


def images(P_, D_):
    Ps, Ds = [], []
    for k in range(NFP):
        ang = -2 * np.pi * k / NFP
        Rz = np.array([[np.cos(ang), -np.sin(ang), 0], [np.sin(ang), np.cos(ang), 0], [0, 0, 1]])
        Ps.append(P_ @ Rz.T)
        Ds.append(D_ @ Rz.T)
        Sm = np.diag([1.0, -1.0, -1.0])
        Ps.append((P_ @ Sm.T) @ Rz.T)
        Ds.append(-(D_ @ Sm.T) @ Rz.T)
    return np.concatenate(Ps), np.concatenate(Ds)


Pall, Dall = images(Pb, Db)
cph, sph = np.cos(ph)[None, :], np.sin(ph)[None, :]
X = np.stack([R * cph, R * sph, Z], -1)
B = np.zeros((Nt, Nf, 3))
Jm = np.zeros((Nt, Nf, 3, 3))
for j0 in range(0, len(Pall), 100):
    p = Pall[j0:j0 + 100]
    dd = Dall[j0:j0 + 100]
    r = X[:, :, None, :] - p[None, None, :, :]
    q = np.sum(r * r, -1)
    y3, y5 = q ** -1.5, q ** -2.5
    dxr = np.cross(dd[None, None], r)
    B += np.sum(dxr * y3[..., None], 2)
    for kk in range(3):
        e = np.zeros(3)
        e[kk] = 1
        dxe = np.cross(dd, e)
        Jm[:, :, :, kk] += np.sum(dxe[None, None] * y3[..., None] - 3 * dxr * (r[..., kk] * y5)[..., None], 2)
eR = np.stack([np.broadcast_to(cph, R.shape), np.broadcast_to(sph, R.shape), 0 * R], -1)
eP = np.stack([np.broadcast_to(-sph, R.shape), np.broadcast_to(cph, R.shape), 0 * R], -1)
eZ = np.stack([0 * R, 0 * R, 1 + 0 * R], -1)
BR, BP, BZ = [np.sum(B * e, -1) for e in (eR, eP, eZ)]
dR = np.einsum("tpik,tpk->tpi", Jm, eR)
dZ = np.einsum("tpik,tpk->tpi", Jm, eZ)
comps = [BR, BP, BZ, np.sum(dR * eR, -1), np.sum(dZ * eR, -1), np.sum(dR * eP, -1), np.sum(dZ * eP, -1),
         np.sum(dR * eZ, -1), np.sum(dZ * eZ, -1)]
jpar = [False, True, True, False, True, True, False, True, False]
print(f"jet on {Nt} x {Nf} ({time.time() - t0:.0f} s)", flush=True)

kj1, kj2 = a.kj
kt = np.fft.fftfreq(Nt, 1.0 / Nt).astype(int)
lp = np.fft.fftfreq(Nf, 1.0 / Nf).astype(int)


def wtn(w_, k, n):
    return np.exp(w_ * (np.abs(k) + KAPPA * np.abs(n)))


rowsJ, nfin_c, eJ = [], [], []
for f, par in zip(comps, jpar):
    F = np.fft.fft2(f) / f.size
    rws = []
    fin = np.zeros_like(F)
    nc = 0.0
    for k in zrange(kj1):
        row = []
        for l in zrange(kj2):
            v = F[k % Nt, l % Nf]
            c = v.real if par else -v.imag
            row.append(int(round(c * 2.0 ** a.sJ)))
            fin[k % Nt, l % Nf] = v.real if par else 1j * v.imag
            nc += abs(c) * wtn(wc, k, NFP * l)
        rws.append(row)
    rowsJ.append(rws)
    nfin_c.append(nc)
    E = F - fin
    eJ.append(float(np.sum((np.abs(E.real) + np.abs(E.imag)) * wtn(w, kt[:, None], NFP * lp[None, :]))))
print("e_J at w (float, grid):", " ".join(f"{x:.2e}" for x in eJ), flush=True)
print("|J_fin| at w':", " ".join(f"{x:.3e}" for x in nfin_c), flush=True)


def encl(x):
    y = x * mp.mpf(2) ** KFX
    return int(mp.floor(y)) - 1, int(mp.ceil(y)) + 1


def dyad(x):
    m = int(mp.nint(mp.mpf(x) * mp.mpf(2) ** KFX))
    return m, m


wq = mp.mpf(mp.fraction(*map(int, a.w.split("/"))))
wcq = mp.mpf(mp.fraction(*map(int, a.wc.split("/"))))
kap = mp.mpf(1) / 10
N1, M, K1, K2, D = a.N1, a.M, a.K1, a.K2, a.D
trig = []
for Nn in (N1, M, P * M):
    trig += [encl(mp.cos(2 * mp.pi / Nn)), encl(mp.sin(2 * mp.pi / Nn))]
exps = [encl(mp.exp(wq)), encl(mp.exp(-wcq)), encl(mp.exp(-(wcq * (N1 - K1)))), encl(mp.exp(wq * (kap * P))),
        encl(mp.exp(-(wcq * (kap * P)))), encl(mp.exp(-(wcq * (kap * (P * M - P * K2))))),
        encl(mp.exp(-((wcq - wq) * (kap * (D + 1)))))]
ims = [dyad(a.margin * (c + n)) for c, n in zip(a.crude, nfin_c)]
ibs = [dyad(a.B) for _ in range(9)]
with open(a.out, "w") as f:
    f.write(f"{P} {N1} {M} {K1} {K2} {D} {Km} {Kn} {kj1} {kj2}\n{s0} {a.sJ}\n")
    for R_ in (rowsR, rowsZ):
        for row in R_:
            f.write(" ".join(map(str, row)) + "\n")
    for rws in rowsJ:
        for row in rws:
            f.write(" ".join(map(str, row)) + "\n")
    f.write(f"{ssrc}\n{ns}\n")
    for s in srcs:
        f.write(" ".join(map(str, s)) + "\n")
    for lo, hi in trig + exps + ims + ibs:
        f.write(f"{lo} {hi}\n")
print(f"wrote {a.out}: grid {N1} x {M}, box {K1} x {K2}, D {D}, approximants {kj1} x {kj2} ({time.time() - t0:.0f} s)")
