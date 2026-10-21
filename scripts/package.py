#!/usr/bin/env python3
"""Create a portable, checksummed source archive without compiler/dependency caches."""
import hashlib
import sys
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEST = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else ROOT.parent / "Maxwell_MGF_Project.zip"


def included(path):
    rel = path.relative_to(ROOT)
    if any(p in {".git", ".lake", "__pycache__", "first-report-build", "report-build", "clean-replay"} for p in rel.parts):
        return False
    if path.name in {".DS_Store", "SHA256SUMS.txt"}:
        return False
    if path.suffix in {".olean", ".ilean", ".aux", ".out"}:
        return False
    return path.is_file()


files = sorted(p for p in ROOT.rglob("*") if included(p))
manifest = ROOT / "SHA256SUMS.txt"
manifest.write_text("".join(hashlib.sha256(p.read_bytes()).hexdigest() + "  " + p.relative_to(ROOT).as_posix() + "\n" for p in files))
with zipfile.ZipFile(DEST, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for p in files + [manifest]:
        z.write(p, "MaxwellMGF/" + p.relative_to(ROOT).as_posix())
with zipfile.ZipFile(DEST) as z:
    assert z.testzip() is None
    lines = z.read("MaxwellMGF/SHA256SUMS.txt").decode().splitlines()
    for line in lines:
        digest, name = line.split("  ", 1)
        assert hashlib.sha256(z.read("MaxwellMGF/" + name)).hexdigest() == digest, name
print(f"Archive: {DEST}\nFiles: {len(files)+1}\nSHA-256: {hashlib.sha256(DEST.read_bytes()).hexdigest()}")
