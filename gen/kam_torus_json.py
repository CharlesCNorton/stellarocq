"""Write the first torus of the KAM certificate as an entry of VMEC++'s
certified-tori reference data.

    python gen/kam_torus_json.py E0 SRC JETS FD FS OUT.json

The torus of the certificate is R = sum c_kl cos(k t + 5 l p), Z = sum s_kl
sin(k t + 5 l p) over the box of its rows, the mantissas at the scale 2^-s0.
The entry holds it in the canonical form R = sum Rc cos(m t - n p),
Z = sum Zs sin(m t - n p) with m = k and n = -5 l, each canonical mode the sum
of its two signs, together with the rotation number, the distance within which
the certificate places an invariant torus, and the digests of the data.
"""
import hashlib
import json
import math
import sys
from fractions import Fraction

e0, srcf, jetsf, fdf, fsf, out = sys.argv[1:7]
t = open(e0).read().split()
i = 0


def nat():
    global i
    i += 1
    return int(t[i - 1])


P, N1, M, K1, K2, D, Km, Kn, Kmu, Knu, Kmg, Kng = [nat() for _ in range(12)]
s0 = nat()


def zrange(K):
    o = []
    for j in range(K, 0, -1):
        o += [j, -j]
    return o + [0]


def rows(A, B):
    return {(k, l): nat() for k in zrange(A) for l in zrange(B)}


C, S = rows(Km, Kn), rows(Km, Kn)
modes, Rc, Zs = [], [], []
for k in range(0, Km + 1):
    for l in range(-Kn, Kn + 1):
        if k == 0 and l < 0:
            continue
        if (k, l) == (0, 0):
            c, s = Fraction(C[(0, 0)], 2 ** s0), Fraction(0)
        else:
            c = Fraction(C[(k, l)] + C[(-k, -l)], 2 ** s0)
            s = Fraction(S[(k, l)] - S[(-k, -l)], 2 ** s0)
        if c == 0 and s == 0:
            continue
        modes.append([k, -P * l])
        Rc.append(float(c))
        Zs.append(float(s))
fs = [Fraction(int(a), int(b)) for a, b in zip(*[iter(open(fsf).read().split())] * 2)]
om = 5 * (337 + math.sqrt(5)) / 1958


def md5(p):
    return hashlib.md5(open(p, "rb").read()).hexdigest()


entry = {
    "name": "kam_0.100",
    "kind": "surface",
    "certificate": "invariant",
    "rotation_per_period": om / P,
    "iota": om,
    "modes": modes,
    "Rc": Rc,
    "Zs": Zs,
    "distance": float(fs[2]),
    "theorem": "Stellarocq KFinal.cert_ok_torus, with its six parts true on the data below",
    "data_md5": {"first_torus": md5(e0), "sources": md5(srcf), "jets": md5(jetsf), "grid_parameters": md5(fdf),
                 "scalar_parameters": md5(fsf)},
}
json.dump(entry, open(out, "w"))
print(f"{len(modes)} modes, R00 {Rc[0]:.9f}, rotation per period {om / P:.12f}, distance {float(fs[2]):.1e}")
