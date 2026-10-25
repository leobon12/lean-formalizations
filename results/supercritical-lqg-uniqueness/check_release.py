#!/usr/bin/env python3
"""Check the sealed release projection against the complete public manifest.

The public manifest is a metadata scrub of the author-approved development
manifest. This release selects all six theorem anchors (DG Theorems 1.3,
1.8(i), 1.8(ii), 1.13 with the exponent (1.5), and the normalizer (1.4)) and
every definition anchor; each must be SEALED. The split-group policy is
checked on the complete metadata projection and the local guard on the
selected anchors.
"""
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

here = Path(__file__).resolve().parent
root = here.parents[1]
spec = importlib.util.spec_from_file_location("frozen_guard", here / "check_frozen_anchors.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
full = json.loads((here / "frozen-anchor-manifest.json").read_text())
source = json.loads((root / "source-manifest.json").read_text())
selected = {row["path"] for mod, row in source["modules"].items()
            if mod.startswith("SupercriticalLQGUniqueness.")}
expected = {
    "existsUnique_isLFPPExponent_v1", "weakLQGMetric_unique_v1",
    "existsUnique_isLFPPNormalizer_v1", "strongLQGMetric_unique_v1",
    "lfpp_tendstoInProbability_v1", "exists_strongLQGMetric_lfppLimit_v1",
}
theorems = {a["id"] for a in full["anchors"] if a["kind"] == "theorem" and a["path"] in selected}
if theorems != expected:
    sys.exit(f"Unexpected release theorem set: {sorted(theorems)}")
unsealed = sorted(a["id"] for a in full["anchors"] if a["id"] in expected and a["state"] != "SEALED")
if unsealed:
    sys.exit(f"Release theorem anchors are not SEALED: {unsealed}")
policy = module.Guard(root, allow_non_module=True)
policy.check_split_groups(full["anchors"])
if policy.errors:
    sys.exit("Full manifest split-policy failure: " + "; ".join(policy.errors))
projection = {**full, "anchors": [a for a in full["anchors"] if a["path"] in selected]}
if any(a["state"] != "SEALED" for a in projection["anchors"]):
    sys.exit("Draft anchor in selected projection")


class ReleaseGuard(module.Guard):
    def check_split_groups(self, anchors):
        # Checked against the complete, unmodified manifest above.
        pass


guard = ReleaseGuard(root, allow_non_module=True)
guard.check(projection)
if guard.errors:
    sys.exit("FROZEN-ANCHOR RELEASE GUARD FAILED:\n" + "\n".join(guard.errors))
print(f"FROZEN-ANCHOR RELEASE GUARD OK: {len(projection['anchors'])} sealed anchors, "
      f"including {len(theorems)} theorem exports; complete split policy OK")
