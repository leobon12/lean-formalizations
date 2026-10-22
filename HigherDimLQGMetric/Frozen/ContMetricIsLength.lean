import HigherDimLQGMetric.Frozen.ContMetricInstMetricSpace
import LQGMetric.Metric.LengthSpace

/-!
# Frozen definition: `ContMetric.IsLength`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 65 (Axiom (I): "`D_h` is a length metric"), [1] §1.2 (length space: for all `z, w` and `ε > 0`
a path of `D`-length at most `D(z, w) + ε`): LQGMetric's generic `MetricGeometry.IsLengthSpace`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `(ℝ^d, D)` is a length space. -/
def ContMetric.IsLength {d : ℕ} (D : ContMetric d) : Prop :=
  LQGMetric.MetricGeometry.IsLengthSpace D.Space

end HigherDimLQGMetric
