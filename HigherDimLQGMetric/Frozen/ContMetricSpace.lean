import HigherDimLQGMetric.Frozen.ContMetric

/-!
# Frozen definition: `ContMetric.Space`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
Carrier of the metric space `(ℝ^d, D)` for `D : ContMetric d` (a type synonym of `ℝ^d`, so that it can
carry the metric `D`; port of LQGMetric's `ContMetric.Space`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `ℝ^d` carrying the metric `D` (a type synonym). -/
def ContMetric.Space {d : ℕ} (_D : ContMetric d) : Type := Rd d

end HigherDimLQGMetric
