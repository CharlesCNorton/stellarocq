"""Summarize what `make audit` reports, so the trust base is not hand-counted.

`Print Assumptions` prints one report per theorem, either a list of axioms or
a line saying the theorem is closed under the global context. The README
states how many axioms sit behind each kind of theorem, and that number is
easy to get wrong by hand: the "Axioms:" header itself parses as a name, and
the miscount looks exactly like a real one.

  make audit > audit.log 2>&1
  python test/audit_summary.py audit.log

It prints the counts and fails if any axiom falls outside the families the
trust base names, which is the claim that actually matters: the classical
reals of the standard library and the primitive integer and float
specifications, and nothing else.
"""

import collections
import re
import sys

# what the trust base allows to appear
FAMILIES = (
    "ClassicalDedekindReals", "ConstructiveCauchyReals",
    "ConstructiveCauchyRealsMult", "ConstructiveEpsilon", "ConstructiveRcomplete",
    "Rdefinitions", "Classical_Prop", "FunctionalExtensionality",
    "PrimInt63", "PrimFloat", "FloatAxioms", "FloatOps", "SpecFloat",
    "Uint63Axioms",
)


def main(path):
    txt = open(path, encoding="utf-8", errors="replace").read()
    blocks = re.split(r"\n(?=Axioms:|Closed under the global context)", txt)
    counts, names, closed = [], set(), 0
    for b in blocks:
        if b.startswith("Closed under the global context"):
            closed += 1
            continue
        if not b.startswith("Axioms:"):
            continue
        ids = set(re.findall(r"^([A-Za-z_][A-Za-z0-9_.]*)\s*:", b, re.M))
        ids.discard("Axioms")          # the header of the block itself
        counts.append(len(ids))
        names |= ids

    reports = len(counts) + closed
    print(f"reports: {reports} ({closed} closed under the global context)")
    for n, k in sorted(collections.Counter(counts).items(), reverse=True):
        print(f"  {k:2d} theorem(s) with {n} axioms")
    print(f"distinct axioms overall: {len(names)}")

    stray = sorted(n for n in names
                   if not any(n.startswith(f + ".") for f in FAMILIES))
    if stray:
        print("\naxioms outside the families the trust base names:")
        for n in stray:
            print(f"  {n}")
        return 1
    print("every axiom is in a family the trust base names")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "audit.log"))
