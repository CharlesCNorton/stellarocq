"""Write an interval Newton certificate for the circle system of Newton.v.

The system is x^2 + y^2 - 1 = 0, x - y = 0, whose zero near the centre
(1/sqrt 2, 1/sqrt 2) the checker establishes with `main --newton`. The
unknowns are mantissas against a common exponent, so the Jacobian, its
approximate inverse A and the approximate inverse B of A are in mantissa
units; the contraction constant K and the entry bound M are claims the
checker tests.

  python gen/newton_circle.py cert.txt [--exp -50] [--radius 30] [--k -16]
"""

import argparse
import math
import pathlib


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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--exp", type=int, default=-50,
                    help="the exponent of both unknowns")
    ap.add_argument("--radius", type=int, default=30,
                    help="the radius as a power of two, in mantissa units")
    ap.add_argument("--k", type=int, default=-16,
                    help="the claimed contraction constant as a power of two")
    ap.add_argument("--offset", type=float, default=0.0,
                    help="move the centre off the zero by this much")
    a = ap.parse_args()
    e = a.exp
    x = 1.0 / math.sqrt(2.0) + a.offset
    m = round(x / 2.0 ** e)
    xc = m * 2.0 ** e
    # the Jacobian in mantissa units at the centre, and its inverse
    j = [[2 * xc * 2.0 ** e, 2 * xc * 2.0 ** e], [2.0 ** e, -(2.0 ** e)]]
    det = j[0][0] * j[1][1] - j[0][1] * j[1][0]
    inv = [[j[1][1] / det, -j[0][1] / det], [-j[1][0] / det, j[0][0] / det]]
    lines = ["STELLAROCQ-NEWTON", "PREC 53", "SYSTEM circle", "N 2",
             f"EXP {e} {e}", f"CENTRE {m} {m}", f"R {2 ** a.radius}",
             f"K 1 {a.k}", "M 1 -49",
             "A " + " ".join("{} {}".format(*dyadic(v)) for row in inv for v in row),
             "B " + " ".join("{} {}".format(*dyadic(v)) for row in j for v in row)]
    pathlib.Path(a.out).write_text("\n".join(lines) + "\n")
    print(f"wrote {a.out}: centre {xc:.17g} twice, radius {2.0 ** (a.radius + e):.3e}")


if __name__ == "__main__":
    main()
