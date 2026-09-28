"""Write the grid parameters of the certificate (KFinal.findata), and
estimates of its scalar parameters (KFinal.fscal) and of the enclosures TR the
grid of the finite twist returns.

    python gen/kam_params.py e0_full2.dat jets_full.dat src_full.dat OUT_FD OUT_FS_EST OUT_TR_EST [--kb 60 60]
    python gen/kam_params.py e0_full2.dat jets_full.dat src_full.dat OUT_FD OUT_FS OUT_TR --kb 60 60 --tr TR

The first writes the grid parameters and estimates of the scalar parameters and
of TR; the second, given the enclosures TR the twist part of the checker wrote,
writes the scalar parameters from them and leaves OUT_FD and OUT_TR alone.

The straightening family b solves L b = tau - T_fin on the finite model the
certificate uses (the jet approximants, the seed Ub of 1 / B_phi and the seed
gs of the frame inverse), truncated to the box (Kmb, Knb) inside the box of gs
and written in sine mantissas at the scale 2^-s0 of the torus. The finite
twist T_fin, its normal and its kmln are evaluated on grids of one period
whose modes carry every coefficient above the float noise; their norms and the
constants of KTwist give the estimates. The claims of the three grid checks
are copied from their data.
"""
import argparse
import math
from fractions import Fraction

import numpy as np

KFX = 192
NFP = 5
KAPPA = 0.1

ap = argparse.ArgumentParser()
ap.add_argument("e0")
ap.add_argument("jets")
ap.add_argument("src")
ap.add_argument("out_fd")
ap.add_argument("out_fs")
ap.add_argument("out_tr")
ap.add_argument("--w0", default="1/20")
ap.add_argument("--d0", default="1/140")
ap.add_argument("--w1", default="3/10")
ap.add_argument("--r", default="1/10000000000")
ap.add_argument("--eps", default="1/100000000000000000000")
ap.add_argument("--delta", default="1/1000000000000000")
ap.add_argument("--kb", type=int, nargs=2, default=[30, 60])
ap.add_argument("--n1t", type=int, default=917)
ap.add_argument("--mt", type=int, default=1318)
ap.add_argument("--grids", type=int, nargs=4, default=[320, 640, 400, 800],
                help="poloidal and one-period toroidal points of the design grid and of the check grid")
ap.add_argument("--np_", type=int, default=60)
ap.add_argument("--nt_", type=int, default=40)
ap.add_argument("--ne", type=int, default=40)
ap.add_argument("--margin", type=float, default=1.02)
ap.add_argument("--mean_margin", type=float, default=2e-4)
ap.add_argument("--tr", default=None,
                help="the enclosures the twist part wrote: the scalar parameters come from them and OUT_FD is not written")
a = ap.parse_args()


def tokens(path):
    with open(path) as f:
        return f.read().split()


class Rd:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def nat(self):
        self.i += 1
        return int(self.t[self.i - 1])

    def rows(self, A, B):
        return [[self.nat() for _ in range(2 * B + 1)] for _ in range(2 * A + 1)]

    def iv(self):
        return (self.nat(), self.nat())


def zrange(K):
    out = []
    for j in range(K, 0, -1):
        out += [j, -j]
    return out + [0]


# ------------------------------------------------------------------ the data of the three grid checks
e = Rd(tokens(a.e0))
P, N1, M, K1, K2, D, Km, Kn, Kmu, Knu, Kmg, Kng = [e.nat() for _ in range(12)]
s0 = e.nat()
rowsR, rowsZ, rowsU, rowsG = e.rows(Km, Kn), e.rows(Km, Kn), e.rows(Kmu, Knu), e.rows(Kmg, Kng)
ssrc = e.nat()
ns = e.nat()
e.i += 6 * ns
ea, eb = e.nat(), e.nat()
e.i += 2 * (6 + 7)
bd = [e.iv() for _ in range(8)]
assert e.i == len(e.t)
assert (P, ea, eb) == (5, 979, -337)

j = Rd(tokens(a.jets))
jP, jN1, jM, jK1, jK2, jD, jKm, jKn, Kj1, Kj2 = [j.nat() for _ in range(10)]
js0, sJ = j.nat(), j.nat()
jrR, jrZ = j.rows(jKm, jKn), j.rows(jKm, jKn)
rowsJ = [j.rows(Kj1, Kj2) for _ in range(9)]
j.nat()
jns = j.nat()
j.i += 6 * jns
j.i += 2 * (6 + 7)
ims = [j.iv() for _ in range(9)]
ibs = [j.iv() for _ in range(9)]
assert j.i == len(j.t)
assert (jP, jKm, jKn, js0) == (P, Km, Kn, s0) and jrR == rowsR and jrZ == rowsZ

s = Rd(tokens(a.src))
sP, sKm, sKn, Kr1, Kr2, N1s, N2s, Ky1, Ky2, sKmu, sKnu, sKmg, sKng = [s.nat() for _ in range(13)]
ss0, sY, sssrc = s.nat(), s.nat(), s.nat()
srR, srZ, srU, srG = s.rows(sKm, sKn), s.rows(sKm, sKn), s.rows(sKmu, sKnu), s.rows(sKmg, sKng)
sns = s.nat()
s.i += 6 * sns + sns * (2 * Ky1 + 1) * (2 * Ky2 + 1) * 2
sa, sb = s.nat(), s.nat()
s.i += 2 * (4 + 6)
scl = [s.iv() for _ in range(4)]
assert s.i == len(s.t)
same = ((sP, sKm, sKn, ss0, sssrc, sns, sa, sb, sKmu, sKnu, sKmg, sKng) == (P, Km, Kn, s0, ssrc, ns, ea, eb, Kmu, Knu, Kmg, Kng)
        and srR == rowsR and srZ == rowsZ and srU == rowsU and srG == rowsG)
print(f"data: torus ({Km}, {Kn}), Ub ({Kmu}, {Knu}), gs ({Kmg}, {Kng}), jets ({Kj1}, {Kj2}), s0 {s0}, sJ {sJ}; "
      f"source data agree with the first-torus data: {same}; claims Mw agree: {scl == bd[:4]}", flush=True)
assert same

w0 = float(Fraction(a.w0))
d0 = float(Fraction(a.d0))
wd = w0 - d0
om = 5 * (337 + math.sqrt(5)) / 1958
jpar = [False, True, True, False, True, True, False, True, False]
Kmb, Knb = a.kb


# ------------------------------------------------------------------ the finite model on a grid of one period
class Grid:
    def __init__(self, Nt, Nf):
        self.Nt, self.Nf = Nt, Nf
        self.kt = np.fft.fftfreq(Nt, 1.0 / Nt).astype(int)
        self.lp = np.fft.fftfreq(Nf, 1.0 / Nf).astype(int)

    def spec_of(self, rows, K1_, L1_, scale, parity):
        F = np.zeros((self.Nt, self.Nf), complex)
        for i, k in enumerate(zrange(K1_)):
            for jj, l in enumerate(zrange(L1_)):
                c = rows[i][jj] / 2.0 ** scale
                if c == 0:
                    continue
                if parity == "c":
                    F[k % self.Nt, l % self.Nf] += c / 2
                    F[-k % self.Nt, -l % self.Nf] += c / 2
                else:
                    F[k % self.Nt, l % self.Nf] += -0.5j * c
                    F[-k % self.Nt, -l % self.Nf] += 0.5j * c
        return F

    def grid(self, F):
        return np.real(np.fft.ifft2(F)) * F.size

    def spec(self, f):
        return np.fft.fft2(f) / f.size

    def dt(self, F):
        return F * (1j * self.kt[:, None])

    def dp(self, F):
        return F * (1j * NFP * self.lp[None, :])

    def norm(self, F, w):
        wt = np.exp(w * (np.abs(self.kt)[:, None] + KAPPA * NFP * np.abs(self.lp)[None, :]))
        return float(np.sum((np.abs(F.real) + np.abs(F.imag)) * wt))

    def Lg(self, f):
        F = self.spec(f)
        return self.grid(om * self.dt(F) + self.dp(F))

    def model(self):
        FR, FZ = self.spec_of(rowsR, Km, Kn, s0, "c"), self.spec_of(rowsZ, Km, Kn, s0, "s")
        FU, FG = self.spec_of(rowsU, Kmu, Knu, s0, "c"), self.spec_of(rowsG, Kmg, Kng, s0, "c")
        FJ = [self.spec_of(rowsJ[i], Kj1, Kj2, sJ, "c" if jpar[i] else "s") for i in range(9)]
        self.R = self.grid(FR)
        self.aR, self.aZ = self.grid(self.dt(FR)), self.grid(self.dt(FZ))
        self.U, self.G = self.grid(FU), self.grid(FG)
        J = [self.grid(F) for F in FJ]
        W = self.R * self.U
        WR = self.U - W * (self.U * J[5])
        WZ = -(W * (self.U * J[6]))
        self.DV = [[WR * J[0] + W * J[3], WZ * J[0] + W * J[4]], [WR * J[2] + W * J[7], WZ * J[2] + W * J[8]]]
        self.sig = J[1]

    def twist(self, bg):
        NR = -self.aZ * self.G + bg * self.aR
        NZ = self.aR * self.G + bg * self.aZ
        MR = self.Lg(NR) - (self.DV[0][0] * NR + self.DV[0][1] * NZ)
        MZ = self.Lg(NZ) - (self.DV[1][0] * NR + self.DV[1][1] * NZ)
        return self.sig * (MR * NZ - MZ * NR), NR, NZ, MR, MZ

    def report(self, bg):
        T, NR, NZ, MR, MZ = self.twist(bg)
        FT = self.spec(T)
        return dict(xNR=self.norm(self.spec(NR), w0), xNZ=self.norm(self.spec(NZ), w0),
                    xKR=self.norm(self.spec(MR), wd), xKZ=self.norm(self.spec(MZ), wd),
                    xT=self.norm(FT, wd), mean=float(FT[0, 0].real))


g1 = Grid(a.grids[0], a.grids[1])
g1.model()
T0g = g1.twist(0 * g1.R)[0]
tau_raw = float(np.mean(T0g))
F = g1.spec(tau_raw - T0g)
dv = om * g1.kt[:, None] + NFP * g1.lp[None, :]
dv[0, 0] = 1.0
Fb = F / (1j * dv)
Fb[0, 0] = 0
# (k, l) and (-k, -l) are one canonical mode: its sine mantissa sits at the positive one
rowsB = [[int(round(float(-2 * Fb[k % g1.Nt, l % g1.Nf].imag) * 2.0 ** s0)) if (k, l) > (0, 0) else 0
          for l in zrange(Knb)] for k in zrange(Kmb)]
bg1 = g1.grid(g1.spec_of(rowsB, Kmb, Knb, s0, "s"))
r1 = g1.report(bg1)
g2 = Grid(a.grids[2], a.grids[3])
g2.model()
r2 = g2.report(g2.grid(g2.spec_of(rowsB, Kmb, Knb, s0, "s")))
print(f"twist: raw mean {tau_raw:.6f}; with b ({Kmb}, {Knb}) on {a.grids[0]} x {a.grids[1]}: "
      + ", ".join(f"{k} {v:.6g}" for k, v in r1.items()), flush=True)
print(f"   on {a.grids[2]} x {a.grids[3]}: " + ", ".join(f"{k} {v:.6g}" for k, v in r2.items()), flush=True)
rr = {k: max(r1[k], r2[k]) for k in r1 if k != "mean"}
mean = r1["mean"]


# ------------------------------------------------------------------ the bounds of KTwist and FinScal
def rows_norm(rows, K1_, L1_, scale, w, dtk=False):
    out = 0.0
    for i, k in enumerate(zrange(K1_)):
        for jj, l in enumerate(zrange(L1_)):
            c = abs(rows[i][jj]) / 2.0 ** scale * (abs(k) if dtk else 1)
            out += c * math.exp(w * (abs(k) + KAPPA * NFP * abs(l)))
    return out


BR, BZ, BU, BG = [x[1] / 2 ** KFX for x in bd[4:]]
ej = [x[1] / 2 ** KFX for x in ibs]
kR0 = rows_norm(rowsR, Km, Kn, s0, w0)
MU = rows_norm(rowsU, Kmu, Knu, s0, w0)
MG = rows_norm(rowsG, Kmg, Kng, s0, w0)
NAR = rows_norm(rowsR, Km, Kn, s0, w0, True)
NAZ = rows_norm(rowsZ, Km, Kn, s0, w0, True)
NB = rows_norm(rowsB, Kmb, Knb, s0, w0)
nj = [rows_norm(rowsJ[i], Kj1, Kj2, sJ, w0) for i in range(9)]


def inv_eps(Y0, q):
    return 2 * Y0 * q / (1 - q) ** 2


eU, eg = inv_eps(MU, BU), inv_eps(MG, BG)
nJ = [nj[i] + ej[i] for i in range(9)]
nU = MU + eU
eW = kR0 * eU
nWf = kR0 * MU
eUP = [eU * nJ[i] + MU * ej[i] for i in range(9)]
nUP = [nU * nJ[i] for i in range(9)]
nUPf = [MU * nj[i] for i in range(9)]
eWUP = [eW * nUP[i] + nWf * eUP[i] for i in range(9)]
eWR, nWRf = eU + eWUP[5], MU + nWf * nUPf[5]
eWZ, nWZf = eWUP[6], nWf * nUPf[6]


def eDVc(eX, nXf, i, jj):
    return (eX * nJ[i] + nXf * ej[i]) + (eW * nJ[jj] + nWf * ej[jj])


def nDVc(nXf, i, jj):
    return nXf * nj[i] + nWf * nj[jj]


eDV = max(eDVc(eWR, nWRf, 0, 3), eDVc(eWZ, nWZf, 0, 4), eDVc(eWR, nWRf, 2, 7), eDVc(eWZ, nWZf, 2, 8))
nDVf = max(nDVc(nWRf, 0, 3), nDVc(nWZf, 0, 4), nDVc(nWRf, 2, 7), nDVc(nWZf, 2, 8))
mg = a.margin
tr_claim = dict(xNR=mg * rr["xNR"], xNZ=mg * rr["xNZ"], xKR=mg * rr["xKR"], xKZ=mg * rr["xKZ"], xT=mg * rr["xT"])
mean_lo = abs(mean) - a.mean_margin
if a.tr:
    with open(a.tr) as f:
        n = int(f.readline())
        ivs = [tuple(int(x) / 2 ** KFX for x in f.readline().split()) for _ in range(n)]
    tr_claim = dict(zip(("xNR", "xNZ", "xKR", "xKZ", "xT"), (ivs[i][1] for i in range(5))))
    lo, hi = ivs[5]
    assert hi < 0 or lo > 0
    mean_lo = min(abs(lo), abs(hi))
    print("enclosures of the twist part: " + ", ".join(f"{k} {v:.6g}" for k, v in tr_claim.items())
          + f", mean in [{lo:.9f}, {hi:.9f}]", flush=True)
A0 = mg * max(NAR, NAZ)
eN = eg * A0
nNf, nkmf = max(tr_claim["xNR"], tr_claim["xNZ"]), max(tr_claim["xKR"], tr_claim["xKZ"])
cL = (abs(om) + 1 / KAPPA) / (math.e * d0)
nNx = nNf + eN
ekm = cL * eN + 2 * (eDV * nNx + nDVf * eN)
nkm = nkmf + ekm
eT = ej[1] * (2 * nkm * nNx) + nj[1] * (2 * (ekm * nNx + nkmf * eN))
G0 = mg * (MG + eg)
N0 = mg * (nNf + eN)
T0 = mg * (tr_claim["xT"] + eT)
tau0 = (mean_lo - eT) / mg
epsx = (MU + eU) * max(BR, BZ)
eps = float(Fraction(a.eps))
print(f"frame: A0 {A0:.5f} (|d_t R| {NAR:.5f}, |d_t Z| {NAZ:.5f}); G0 {G0:.4f} (|gs| {MG:.4f}, e_g {eg:.2e}); "
      f"N0 {N0:.4f}; |b| {NB:.4f}; |U - Ub| <= {eU:.2e}; |J_fin| {[round(x, 4) for x in nj]}", flush=True)
print(f"twist: e_S {ej[1]:.1e} e_DV {eDV:.2e} |DV_fin| {nDVf:.3f} e_N {eN:.2e} cL {cL:.1f} e_kmln {ekm:.3e} "
      f"=> e_T {eT:.3e}; T0 {T0:.5f} tau0 {tau0:.5f}", flush=True)
print(f"error: (|Ub| + e_U) max(B_R, B_Z) = {epsx:.3e} <= eps0 {eps:.1e}: {epsx <= eps}", flush=True)
assert epsx <= eps and tau0 > 0 and BU < 1 and BG < 1


def q_up(x, digits=6):
    e10 = math.floor(math.log10(abs(x))) - digits
    return Fraction(math.ceil(x / 10.0 ** e10 * (1 + 1e-12))) * Fraction(10) ** e10


def q_down(x, digits=6):
    e10 = math.floor(math.log10(abs(x))) - digits
    return Fraction(math.floor(x / 10.0 ** e10 * (1 - 1e-12))) * Fraction(10) ** e10


def dyad_up(iv):
    return Fraction(iv[1], 2 ** KFX)


w0q, d0q, w1q = Fraction(a.w0), Fraction(a.d0), Fraction(a.w1)
assert 6 * d0q < w0q <= w1q
claims = [dyad_up(x) for x in bd[:4]] + [dyad_up(x) for x in bd[4:]] + [dyad_up(x) for x in ims] + \
         [dyad_up(x) for x in ibs]
bT = (Kj1 + (Km + Kmu + (Kmu + Kj1) + Kj1) + 2 * (max(Kmg, Kmb) + Km),
      Kj2 + (Kn + Knu + (Knu + Kj2) + Kj2) + 2 * (max(Kng, Knb) + Kn))
assert 2 * bT[0] < a.n1t and 2 * (NFP * bT[1] + NFP - 1) < NFP * a.mt
if not a.tr:
    with open(a.out_fd, "w") as f:
        for x in [w0q, d0q, w1q] + claims:
            f.write(f"{x.numerator} {x.denominator}\n")
        f.write(f"{Kmb} {Knb}\n")
        for row in rowsB:
            f.write(" ".join(map(str, row)) + "\n")
        f.write(f"{a.n1t} {a.mt} {a.np_} {a.nt_} {a.ne}\n")

scal = [Fraction(a.r), Fraction(a.eps), Fraction(a.delta), q_up(A0), q_up(G0), q_up(N0), q_up(T0), q_down(tau0),
        q_up(mg * A0), q_up(mg * G0), q_up(mg * N0), q_up(mg * NB), q_up(mg * T0), q_down(tau0 / mg)]
with open(a.out_fs, "w") as f:
    for x in scal:
        f.write(f"{x.numerator} {x.denominator}\n")


def encl(lo, hi):
    return max(math.floor(lo * 2 ** KFX) - 1, 0) if lo >= 0 else math.floor(lo * 2 ** KFX) - 1, math.ceil(hi * 2 ** KFX) + 1


if not a.tr:
    tr = [encl(0, tr_claim[k]) for k in ("xNR", "xNZ", "xKR", "xKZ", "xT")] + \
         [encl(mean - a.mean_margin, mean + a.mean_margin)]
    with open(a.out_tr, "w") as f:
        f.write("6\n")
        for lo, hi in tr:
            f.write(f"{lo} {hi}\n")
print(f"wrote {a.out_fd} (b ({Kmb}, {Knb}), twist box {bT}, grid {a.n1t} x {a.mt}), {a.out_fs}, {a.out_tr}")
print("scalar estimates:", [f"{float(x):.6g}" for x in scal])
