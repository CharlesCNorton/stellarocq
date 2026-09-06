"""One reader of the certificate grammar, for the tools that report numbers.

A bound line is eight integers ordinarily, ten when the file carries a third
varied slot, and ten again when it carries a Taylor bound, with the two
ten-integer forms meaning different things. The analysis tools used to find
bound lines by looking for a run of eight integer-shaped fields and to read
the cell bound from a fixed offset, which reads the wrong pair out of either
ten-integer form and reads a coefficient row of a later node block as a bound
line. This parses the header, which is what says how wide a bound line is, and
then reads the file by that width.

[FORMAT.md](../FORMAT.md) is the grammar. This is the one implementation of it
on the reporting side.

gen/verify_cert.py deliberately does not use this. It exists to read a
certificate independently of the generator and compare it against a wout, and
a shared parser would give the generator and its guard one implementation to
be wrong in together.

  from certfile import Cert
  c = Cert.read("cells_tightened.txt")
  for node in c.nodes:
      for cell in node.cells:
          c.cell_bound(cell.s), c.centre_bound(cell.s)
"""

import pathlib

# the OUTPUT names whose line carries a mode pair after the name
OUTPUT_WITH_MODE = ("harmonic", "covariant", "covariant-sin", "boozer")

# how many integral exponents a PROFILE name carries inline
PROFILE_EXTRA = {"TWOPOWER": 2, "RATIONAL": 2, "TWOPOWERGS": 3,
                 "TWOLORENTZ": 4}


class Cell:
    """One cell's three bound lines, in component order."""

    __slots__ = ("s", "u", "v")

    def __init__(self, s, u, v):
        self.s, self.u, self.v = s, u, v

    def __iter__(self):
        return iter((self.s, self.u, self.v))


class Node:
    """One node block: where it sits, and the cells it carries."""

    __slots__ = ("s", "du", "cells", "same")

    def __init__(self, s, du, same):
        self.s, self.du, self.same, self.cells = s, du, same, []


class Cert:
    """A parsed certificate."""

    def __init__(self):
        self.kind = None
        self.prec = 0
        self.lasym = False
        self.profile = ""
        self.slots = (1, 2)
        self.slot3 = None
        self.taylor = False
        self.output = ""
        self.modes = []
        self.angles = []
        self.nodes = []

    # ---- what the header decides about a bound line --------------------

    @property
    def cells_mode(self):
        return self.kind == "STELLAROCQ-CCERT"

    @property
    def bound_width(self):
        """Integers per bound line: ten with a third slot or a Taylor bound."""
        return 10 if (self.slot3 is not None or self.taylor) else 8

    @property
    def cell_index(self):
        """Where the cell bound's pair starts.

        An ordinary line is N0 q0 NDu qDu NDv qDv Nc qc, and a third slot adds
        its own pair after that, so the cell bound stays at six. A Taylor line
        is N0 q0 Nu qu Nuu quu Nv qv Nc qc, which pushes it to eight.
        """
        return 8 if self.taylor else 6

    def centre_bound(self, line):
        """The claimed bound at the cell centre, which every form puts first."""
        return line[0] * 2.0 ** line[1]

    def cell_bound(self, line):
        """The claimed bound over the whole cell."""
        i = self.cell_index
        return line[i] * 2.0 ** line[i + 1]

    # ---- reading -------------------------------------------------------

    @classmethod
    def read(cls, path):
        return cls._parse(pathlib.Path(path).read_text().split())

    @classmethod
    def _parse(cls, toks):
        c = cls()
        i = 0

        def nxt():
            nonlocal i
            v = toks[i]
            i += 1
            return v

        def peek():
            return toks[i] if i < len(toks) else None

        def expect(w):
            got = nxt()
            if got != w:
                msg = f"expected {w!r}, found {got!r} at token {i}"
                raise ValueError(msg)

        def int_():
            return int(nxt())

        def dyad():
            return int_() * 2.0 ** int_()

        c.kind = nxt()
        if c.kind not in ("STELLAROCQ-CERT", "STELLAROCQ-CCERT"):
            msg = f"not a certificate: {c.kind!r}"
            raise ValueError(msg)
        nxt()                                   # version
        expect("PREC")
        c.prec = int_()
        expect("LASYM")
        c.lasym = nxt() == "1"
        expect("PROFILE")
        c.profile = nxt()
        for _ in range(PROFILE_EXTRA.get(c.profile, 0)):
            int_()
        expect("SLOTS")
        c.slots = (int_(), int_())
        if peek() == "SLOT3":
            nxt()
            c.slot3 = (int_(), int_())
        if peek() == "TAYLOR":
            nxt()
            c.taylor = True
        expect("OUTPUT")
        c.output = nxt()
        if c.output in OUTPUT_WITH_MODE:
            int_(), int_()
        expect("MODES")
        K = int_()
        c.modes = [(int_(), int_()) for _ in range(K)]
        expect("PHIP")
        dyad()
        expect("AM")
        expect("21")
        for _ in range(21):
            dyad()
        if not c.cells_mode:
            for tag in ("EPS_S", "EPS_U", "EPS_V"):
                expect(tag)
                dyad()

        expect("NANGLES")
        na = int_()
        for _ in range(na):
            u, v = dyad(), dyad()
            du = int_() if c.cells_mode else 0
            dv = int_() if c.cells_mode else 0
            c.angles.append((u, v, du, dv))

        expect("NNODES")
        nb = int_()
        width = c.bound_width
        for _ in range(nb):
            expect("NODE")
            same = peek() == "SAME"
            if same:
                nxt()
            expect("S")
            s = dyad()
            du = None
            if peek() == "DU":
                nxt()
                du = int_()
            if peek() == "AMLOCAL":
                nxt()
                expect("21")
                for _ in range(21):
                    dyad()
            node = Node(s, du, same)
            if not same:
                expect("SNODES")
                for _ in range(3):
                    dyad()
                expect("SHALF")
                for _ in range(2):
                    dyad()
                expect("IOTA")
                for _ in range(2):
                    dyad()
                blocks = [("RNODES", 3), ("ZNODES", 3), ("LHALF", 2)]
                if c.lasym:
                    blocks += [("RNODES_A", 3), ("ZNODES_A", 3),
                               ("LHALF_A", 2)]
                for tag, rows in blocks:
                    expect(tag)
                    for _ in range(rows * K):
                        dyad()
            if peek() == "WCOEF":
                nxt()
                m = int_()
                if m != K:
                    msg = f"WCOEF {m}, the certificate has {K} modes"
                    raise ValueError(msg)
                for _ in range(K + 2):
                    dyad()
            if peek() == "FZERO":
                nxt()
                dyad()
            if c.cells_mode:
                expect("CELLS")
                m = int_()
                if m != na:
                    msg = f"CELLS {m}, NANGLES {na}"
                    raise ValueError(msg)
                for _ in range(m):
                    triple = []
                    for _ in range(3):
                        triple.append(tuple(int_() for _ in range(width)))
                    node.cells.append(Cell(*triple))
            c.nodes.append(node)

        if i != len(toks):
            msg = f"{len(toks) - i} tokens left unread"
            raise ValueError(msg)
        return c

    # ---- what the reporting tools ask for -------------------------------

    def worst_centre(self):
        """The largest centre bound over every cell of every node."""
        return max((self.centre_bound(line)
                    for node in self.nodes
                    for cell in node.cells
                    for line in cell), default=0.0)

    def worst_centre_per_node(self):
        """The same, per node block, in file order."""
        return [max((self.centre_bound(line)
                     for cell in node.cells for line in cell), default=0.0)
                for node in self.nodes]

    def centre_per_cell(self):
        """Per node block, the three components' centre bound of each cell."""
        return [[[self.centre_bound(line) for line in cell]
                 for cell in node.cells]
                for node in self.nodes]

    def worst_cell_by_component(self):
        """The largest cell bound of each of the three components."""
        worst = [0.0, 0.0, 0.0]
        for node in self.nodes:
            for cell in node.cells:
                for k, line in enumerate(cell):
                    worst[k] = max(worst[k], self.cell_bound(line))
        return worst

    def radii(self):
        """The radius each node block is evaluated at, in file order."""
        return [node.s for node in self.nodes]

    def angle_centres(self):
        """The centre of each shared cell, in radians, in listed order."""
        return [(u, v) for u, v, _, _ in self.angles]
