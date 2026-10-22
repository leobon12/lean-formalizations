import HigherDimLQGMetric.Frozen.ContMetricPt
import HigherDimLQGMetric.Frozen.ContMetricInstMetricSpace
import LQGMetric.Metric.LengthSpace

/-!
# Frozen definition: `ContMetric.internal`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 60 ("For an open set `U`, `D(·, ·; U)` is the internal metric"), [1] §1.2 (definition of the
internal metric: the infimum of `D`-lengths of paths in `U` joining `z` and `w`): LQGMetric's generic
`MetricGeometry.internalEDist` (infimum of the lengths, i.e. variations, of continuous paths inside the
set), in `[0, ∞]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The internal metric `D(z, w; U) ∈ [0, ∞]`. -/
def ContMetric.internal {d : ℕ} (D : ContMetric d) (U : Set (Rd d)) (z w : Rd d) : ℝ≥0∞ :=
  LQGMetric.MetricGeometry.internalEDist (X := D.Space) (D.pt '' U) (D.pt z) (D.pt w)

end HigherDimLQGMetric
