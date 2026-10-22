import HigherDimLQGMetric.Frozen.DistRd
import HigherDimLQGMetric.Frozen.TestAffinePull

/-!
# Frozen definition: `affineComp`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 76–78 (Axiom (IV): `h(r·+z)`), l. 99 (translation covariance, `h(·+z)` = `affineComp 1 z h`): the
distributional pullback `⟨h(r·+z), φ⟩ = r^{-d} ⟨h, φ((·-z)/r)⟩` (change of variables `y = rx + z` in
`ℝ^d`, `r > 0`). Port of LQGMetric's `affineComp` (factor `r^{-2}` there).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h(r · + z)`: `⟨h(r · + z), φ⟩ = r^{-d} ⟨h, φ((· - z)/r)⟩` (used for `r > 0`). -/
def affineComp {d : ℕ} (r : ℝ) (z : Rd d) (h : DistRd d) : DistRd d :=
  (r ^ d)⁻¹ • h.comp (testAffinePull r z)

end HigherDimLQGMetric
