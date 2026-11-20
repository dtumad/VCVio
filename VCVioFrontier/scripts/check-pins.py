#!/usr/bin/env python3
"""Check the nested lockfiles or update them from a local PolyFun commit (Python 3.11+)."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ROOT / ".lake/packages"
PINNED = ("PolyFun", "PolyFunFrontier", "cslib-frontier", "cslib", "mathlib")


def revisions(manifest):
    return {p["name"].strip("«»"): p.get("rev") for p in json.loads(manifest)["packages"]}


def check():
    ours = revisions((ROOT / "lake-manifest.json").read_text())
    declared = {r["name"]: r.get("rev") for r in
                tomllib.loads((ROOT / "lakefile.toml").read_text())["require"]}
    errors = []
    for name in PINNED:
        if not re.fullmatch("[0-9a-f]{40}", declared.get(name) or "") or declared[name] != ours.get(name):
            errors.append(f"{name} requires one full revision shared by lakefile and manifest")
    if ours.get("PolyFun") != ours.get("PolyFunFrontier"):
        errors.append("PolyFun and its nested package must come from the same commit")

    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    for peer in (PACKAGES / "PolyFunFrontier/PolyFunFrontier", PACKAGES / "cslib-frontier"):
        if (peer / "lean-toolchain").read_text().strip() != toolchain:
            errors.append(f"lean-toolchain differs from {peer.name}")
        for name, rev in revisions((peer / "lake-manifest.json").read_text()).items():
            # PolyFunFrontier's local parent path resolves to our pinned PolyFun checkout.
            if rev is not None and ours.get(name) != rev:
                errors.append(f"{name} must match {peer.name}'s lockfile at {rev}")
    stable = revisions((ROOT.parent / "lake-manifest.json").read_text())
    for name in ("VCVioFrontier", "PolyFunFrontier", "cslib-frontier"):
        if name in stable:
            errors.append(f"stable VCVio unexpectedly resolves {name}")
    if errors:
        sys.exit("\n".join(errors))
    print(f"VCVioFrontier agrees with PolyFun {ours['PolyFun'][:12]} and "
          f"cslib-frontier {ours['cslib-frontier'][:12]} on {toolchain}")


def sync(repo, ref):
    def git(*args):
        return subprocess.check_output(["git", "-C", repo, *args], text=True)

    sha = git("rev-parse", "--verify", ref + "^{commit}").strip()
    pins = revisions(git("show", sha + ":PolyFunFrontier/lake-manifest.json"))
    pins.update(PolyFun=sha, PolyFunFrontier=sha)
    config = ROOT / "lakefile.toml"
    contents = config.read_text()
    for name in PINNED:
        pattern = rf'(^name = "{re.escape(name)}"\n[^\[]*?^rev = ")[0-9a-f]{{40}}(")'
        contents, count = re.subn(pattern, rf"\g<1>{pins[name]}\2", contents, flags=re.M)
        if count != 1:
            sys.exit(f"expected exactly one revision for {name}")
    toolchain = git("show", sha + ":PolyFunFrontier/lean-toolchain")
    config.write_text(contents)
    (ROOT / "lean-toolchain").write_text(toolchain)
    subprocess.run(["lake", "update", "--keep-toolchain", *PINNED], cwd=ROOT, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sync-from", nargs=2, metavar=("POLYFUN_CHECKOUT", "REF"),
                        help="resolve the pins from this PolyFun commit, then run the check")
    args = parser.parse_args()
    if args.sync_from:
        sync(*args.sync_from)
    check()
