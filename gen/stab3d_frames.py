"""The frames of the three-dimensional stability check (colloc3d, Final3d).

    python gen/stab3d_frames.py OUT

For each of the 12 segments s in [1/4 + k/16, 1/4 + (k+1)/16] of the
manufactured problem of mms_colloc.py, case 3d, a frame W_k and its binary64
inverse D_k, 14 rows each, as hexadecimal binary64 numbers. The checker
encloses W_k^-1 from W_k and D_k itself, and no number here is trusted.

The linearized rows advance the state z = (X, Pm d) of a node by
z' = (I + h N) z + h zeta (Recur.v, Step.v). The blocks are the Jacobian of
the node rule at the manufactured solution, by complex steps: with A, B and C
the blocks of the five radial rows toward the nodes s - h, s and s + h, and
of the four poloidal rows likewise,

  Pp = h^2 C,  Pm = h^2 A,  Sx = A + B + C   (radial rows),
  Up = h C,    V = B + C                     (poloidal rows),

M = [Pp; Up], Q = (Pm(s + h) - Pp(s)) / h, and N is Step.v's Nmat. W_k is
taken at the segment's middle s_k, rounded to a multiple of 2^-14, with the
step h = 2^-14: the coordinates (X, c), c = N_U^T K^-1 [p; -V(s - h) X], N_U
an orthonormal basis of the kernel of Up(s - h) and
K = [Pm(s); Up(s - h) - h V(s - h)], scaled by the inverse of the diagonal
matrix of the Perron vector of the off-diagonal part of |W N W^-1|.

The paper's frames:

  python gen/stab3d_frames.py colloc3d/cert/frames3d.txt
"""
import math
import pathlib
import sys

import numpy as np
import scipy.linalg as sla

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import manufactured_solution as mms  # noqa: E402
import mms_colloc as mc  # noqa: E402

MU0 = 4.0e-7 * math.pi
CASE, MMAX = mc.cases(mms)["3d"]
MODES = mc.physics_modes(CASE.nfp, MMAX)
MM = np.array([m for m, _ in MODES], float)
NN = np.array([n for _, n in MODES], float)
ODD = (MM % 2) == 1
PHIP = float(CASE.phip)
AM = [CASE.pres_scale * c for c in CASE.am]
MU0PP = MU0 * sum(i * a for i, a in enumerate(AM) if i > 0)  # p is linear in s
NSEG = 12


def exact(s):
    """The R, Z and lambda coefficients of the mapping at radius s."""
    c = mc.coefficient_rows(mms, CASE, [s], CASE.nfp, MODES)
    return c["rmnc"][0], c["zmns"][0], c["lmns"][0]


def iota(s):
    return sum(c * s**i for i, c in enumerate(CASE.iota_coeff))


def half(ya, yb, sa, sb, sh):
    """The half-grid value and slope of every coefficient."""
    ev, ed = 0.5 * (ya + yb), (yb - ya) / (sb - sa)
    qa, qb = ya / math.sqrt(sa), yb / math.sqrt(sb)
    ov = math.sqrt(sh) * 0.5 * (qa + qb)
    od = math.sqrt(sh) * (qb - qa) / (sb - sa) + ov / (2.0 * sh)
    return np.where(ODD, ov, ev), np.where(ODD, od, ed)


def series(val, ds, cosk, sink, even):
    m, n = MM, NN
    k0, k1 = (cosk, sink) if even else (sink, cosk)
    su, sv = (-m, n) if even else (m, -n)
    return {"0": val @ k0, "s": ds @ k0, "u": (su * val) @ k1, "v": (sv * val) @ k1,
            "su": (su * ds) @ k1, "sv": (sv * ds) @ k1,
            "uu": (-m * m * val) @ k0, "uv": (m * n * val) @ k0, "vv": (-n * n * val) @ k0}


def lseries(lam, cosk, sink):
    m, n = MM, NN
    k0, k1 = sink, cosk
    su, sv = m, -n
    return {"u": (su * lam) @ k1, "v": (sv * lam) @ k1, "uu": (-m * m * lam) @ k0,
            "uv": (m * n * lam) @ k0, "vv": (-n * n * lam) @ k0}


def field(Ra, Rb, Za, Zb, lam, io, sa, sb, sh, u, v):
    """The half-point field of Physics.v between the nodes sa and sb."""
    arg = MM * u - NN * v
    cosk, sink = np.cos(arg), np.sin(arg)
    R = series(*half(Ra, Rb, sa, sb, sh), cosk, sink, True)
    Z = series(*half(Za, Zb, sa, sb, sh), cosk, sink, False)
    L = lseries(lam, cosk, sink)
    tau = R["u"] * Z["s"] - R["s"] * Z["u"]
    g = R["0"] * tau
    tau_u = R["uu"] * Z["s"] + R["u"] * Z["su"] - (R["su"] * Z["u"] + R["s"] * Z["uu"])
    tau_v = R["uv"] * Z["s"] + R["u"] * Z["sv"] - (R["sv"] * Z["u"] + R["s"] * Z["uv"])
    g_u = R["u"] * tau + R["0"] * tau_u
    g_v = R["v"] * tau + R["0"] * tau_v
    guu = R["u"] ** 2 + Z["u"] ** 2
    guv = R["u"] * R["v"] + Z["u"] * Z["v"]
    gvv = R["v"] ** 2 + Z["v"] ** 2 + R["0"] ** 2
    gsu = R["s"] * R["u"] + Z["s"] * Z["u"]
    gsv = R["s"] * R["v"] + Z["s"] * Z["v"]
    gsu_u = R["su"] * R["u"] + R["s"] * R["uu"] + Z["su"] * Z["u"] + Z["s"] * Z["uu"]
    gsu_v = R["sv"] * R["u"] + R["s"] * R["uv"] + Z["sv"] * Z["u"] + Z["s"] * Z["uv"]
    gsv_u = R["su"] * R["v"] + R["s"] * R["uv"] + Z["su"] * Z["v"] + Z["s"] * Z["uv"]
    gsv_v = R["sv"] * R["v"] + R["s"] * R["vv"] + Z["sv"] * Z["v"] + Z["s"] * Z["vv"]
    guu_v = 2 * (R["u"] * R["uv"] + Z["u"] * Z["uv"])
    guv_u = R["uu"] * R["v"] + R["u"] * R["uv"] + Z["uu"] * Z["v"] + Z["u"] * Z["uv"]
    guv_v = R["uv"] * R["v"] + R["u"] * R["vv"] + Z["uv"] * Z["v"] + Z["u"] * Z["vv"]
    gvv_u = 2 * (R["v"] * R["uv"] + Z["v"] * Z["uv"] + R["0"] * R["u"])
    bu_num = io - L["v"]
    bv_num = 1.0 + L["u"]
    Bu = PHIP * bu_num / g
    Bv = PHIP * bv_num / g
    g2 = g * g
    Bu_u = PHIP * (-L["uv"] * g - bu_num * g_u) / g2
    Bv_u = PHIP * (L["uu"] * g - bv_num * g_u) / g2
    Bu_v = PHIP * (-L["vv"] * g - bu_num * g_v) / g2
    Bv_v = PHIP * (L["uv"] * g - bv_num * g_v) / g2
    B_u = guu * Bu + guv * Bv
    B_v = guv * Bu + gvv * Bv
    B_s_u = gsu_u * Bu + gsu * Bu_u + (gsv_u * Bv + gsv * Bv_u)
    B_s_v = gsu_v * Bu + gsu * Bu_v + (gsv_v * Bv + gsv * Bv_v)
    B_u_v = guu_v * Bu + guu * Bu_v + (guv_v * Bv + guv * Bv_v)
    B_v_u = guv_u * Bu + guv * Bu_u + (gvv_u * Bv + gvv * Bv_u)
    return {"Bu": Bu, "Bv": Bv, "B_u": B_u, "B_v": B_v, "B_s_u": B_s_u,
            "B_s_v": B_s_v, "Js": B_v_u - B_u_v}


def unpack(x):
    """The 9 unknowns of a node as R (5) and Z (5, the (0,0) entry zero)."""
    R = x[:5]
    Z = np.concatenate([[0.0 * x[0]], x[5:]])
    return R, Z


class Node:
    """The nine rows of the node rule at the collocation points."""

    def __init__(self, pts_s, pts_u):
        self.ps, self.pu = pts_s, pts_u

    def residual(self, s, h, x0, x1, x2, lm, lp):
        R0, Z0 = unpack(x0)
        R1, Z1 = unpack(x1)
        R2, Z2 = unpack(x2)
        im, ip = iota(s - h / 2), iota(s + h / 2)
        out = []
        for u, v in self.ps:
            qm = field(R0, R1, Z0, Z1, lm, im, s - h, s, s - h / 2, u, v)
            qp = field(R1, R2, Z1, Z2, lp, ip, s, s + h, s + h / 2, u, v)
            avg = lambda k: 0.5 * (qm[k] + qp[k])  # noqa: E731
            dif = lambda k: (qp[k] - qm[k]) / h  # noqa: E731
            out.append((avg("B_s_v") - dif("B_v")) * avg("Bv")
                       - (dif("B_u") - avg("B_s_u")) * avg("Bu") - MU0PP)
        for u, v in self.pu:
            qp = field(R1, R2, Z1, Z2, lp, ip, s, s + h, s + h / 2, u, v)
            out.append(-(qp["Js"] * qp["Bv"]))
        return np.array(out)

    def blocks(self, s, h, step=1e-30):
        """The 9 x 9 Jacobian blocks toward x_{j-1}, x_j, x_{j+1} at the exact
        solution."""
        xs = []
        for t in (s - h, s, s + h):
            R, Z, _ = exact(t)
            xs.append(np.concatenate([R, Z[1:]]))
        lm = exact(s - h / 2)[2]
        lp = exact(s + h / 2)[2]
        out = []
        for node in range(3):
            Bk = np.zeros((9, 9))
            for k in range(9):
                xx = [x.astype(complex) for x in xs]
                xx[node][k] += 1j * step
                Bk[:, k] = np.imag(self.residual(s, h, xx[0], xx[1], xx[2], lm, lp)) / step
            out.append(Bk)
        return out


def reduced(node, s, h, cache):
    """Pp, Pm, Sx, Up and V at (s, h)."""
    key = (round(s / h * 2), h)
    if key in cache:
        return cache[key]
    A, B, C = node.blocks(s, h)
    r = {"Pp": h * h * C[:5], "Pm": h * h * A[:5], "S": (A + B + C)[:5],
         "Up": h * C[5:], "V": (B + C)[5:]}
    cache[key] = r
    return r


def generator(node, s, h, cache):
    """N(s, h) on the state (X, p)."""
    r0 = reduced(node, s, h, cache)
    r1 = reduced(node, s + h, h, cache)
    M = np.vstack([r0["Pp"], r0["Up"]])
    Mi = np.linalg.inv(M)
    Q = (r1["Pm"] - r0["Pp"]) / h
    I5 = np.vstack([np.eye(5), np.zeros((4, 5))])
    Z5 = np.vstack([np.zeros((5, 4)), np.eye(4)])
    SV = np.vstack([h * r0["S"], r0["V"]])
    N = np.zeros((14, 14))
    N[:9, :9] = -Mi @ SV
    N[:9, 9:] = Mi @ I5
    N[9:, :9] = -r1["Pm"] @ Mi @ np.vstack([r0["S"], np.zeros((4, 9))]) - Q @ Mi @ Z5 @ r0["V"]
    N[9:, 9:] = Q @ Mi @ I5
    return N


def coords(node, s, h, cache):
    """W at radius s before balancing: (X, p) -> (X, c)."""
    r0 = reduced(node, s, h, cache)
    rm = reduced(node, s - h, h, cache)
    K = np.vstack([r0["Pm"], rm["Up"] - h * rm["V"]])
    Ki = np.linalg.inv(K)
    NU = sla.null_space(rm["Up"])
    W = np.zeros((14, 14))
    W[:9, :9] = np.eye(9)
    W[9:, 9:] = NU.T @ Ki @ np.vstack([np.eye(5), np.zeros((4, 5))])
    W[9:, :9] = -NU.T @ Ki @ np.vstack([np.zeros((5, 9)), rm["V"]])
    return W


def perron(Nm):
    """The diagonal matrix of the Perron vector of the off-diagonal part of
    |Nm|, scaled to largest entry 1."""
    A = np.abs(Nm.copy())
    np.fill_diagonal(A, 0.0)
    w, V = np.linalg.eig(A)
    k = int(np.argmax(w.real))
    d = np.abs(V[:, k].real)
    d = np.maximum(d, 1e-12 * d.max())
    return np.diag(d / d.max())


def frames(node):
    cache = {}
    edges = [0.25 + j / 16 for j in range(NSEG + 1)]
    Ws = []
    for a, b in zip(edges[:-1], edges[1:]):
        hW = 2.0**-14
        sm = round(0.5 * (a + b) / hW) * hW
        W = coords(node, sm, hW, cache)
        Nm = generator(node, sm, hW, cache)
        Ws.append(np.linalg.inv(perron(W @ Nm @ np.linalg.inv(W))) @ W)
    return Ws


def main():
    ps, pu, _, _ = mc.collocation(MODES, CASE.nfp, False)
    node = Node([tuple(p) for p in ps], [tuple(p) for p in pu])
    with open(sys.argv[1], "w") as f:
        for W in frames(node):
            D = np.linalg.inv(W)
            for M in (W, D):
                for row in M:
                    f.write(" ".join(float(x).hex() for x in row) + "\n")
            print(f"|W| {np.abs(W).sum(axis=1).max():.4e}  |D| {np.abs(D).sum(axis=1).max():.4e}  "
                  f"|I - D W| {np.abs(np.eye(14) - D @ W).sum(axis=1).max():.3e}", flush=True)


if __name__ == "__main__":
    main()
