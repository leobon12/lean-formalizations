import HigherDimLQGMetric.Frozen.ContMetricSpace

/-!
# Frozen definition: `ContMetric.pt`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
The identity `ℝ^d → (ℝ^d, D)` (port of LQGMetric's `ContMetric.pt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The identity `ℝ^d → D.Space`. -/
def ContMetric.pt {d : ℕ} (D : ContMetric d) : Rd d → D.Space := id

end HigherDimLQGMetric
