import HigherDimLQGMetric.Frozen.ContMetricSpace
import Mathlib.Topology.MetricSpace.Basic

/-!
# Frozen definition: `ContMetric.instMetricSpace`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
The metric space `(ℝ^d, D)`: `dist x y = D(x, y)` (the remaining structure is mathlib's default derived
from `dist`). Declared as an instance (`@[instance_reducible, instance] def`, what `instance` produces).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `(ℝ^d, D)` as a metric space: `dist x y = D(x, y)`. -/
@[instance_reducible, instance]
def ContMetric.instMetricSpace {d : ℕ} (D : ContMetric d) : MetricSpace D.Space where
  dist x y := D.1 (x, y)
  dist_self x := D.2.self_eq_zero x
  dist_comm x y := D.2.symm x y
  dist_triangle x y z := D.2.triangle x y z
  eq_of_dist_eq_zero {x y} h := D.2.eq_of_eq_zero x y h

end HigherDimLQGMetric
