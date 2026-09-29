"""SHA-256 of every file behind the paper's results.

Writes one line per file, the digest and the path relative to the directory
given, sorted by path, in the format `sha256sum -c` reads:

  python gen/manifest.py DIR > SHA256SUMS
  sha256sum -c SHA256SUMS            (from DIR)

DIR holds the wout files, the certificates the generators wrote from them and
the checker binary the verdicts came from.
"""

import hashlib
import pathlib
import sys


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def main():
    root = pathlib.Path(sys.argv[1])
    for p in sorted(q for q in root.rglob("*") if q.is_file()):
        rel = p.relative_to(root).as_posix()
        if rel == "SHA256SUMS":
            continue
        print(f"{digest(p)}  {rel}")


if __name__ == "__main__":
    main()
