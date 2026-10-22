import HigherDimLQGMetric.Frozen.IsMetricFn
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Frozen definition: `IsContinuousMetric`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 60–61 ("All metrics ... are finite and induce the Euclidean topology"), [1] §1.2 ("continuous
metric"): a metric that is continuous on `ℝ^d × ℝ^d` (so `D`-balls are open) and whose small balls are
Euclidean-small (so Euclidean balls are `D`-open); together: `D` induces the Euclidean topology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- A continuous metric on `ℝ^d` inducing the Euclidean topology. -/
structure IsContinuousMetric {d : ℕ} (D : C(Rd d × Rd d, ℝ)) : Prop extends IsMetricFn D where
  euclidean_of_small : ∀ x, ∀ ε > 0, ∃ δ > 0, ∀ y, D (x, y) < δ → ‖x - y‖ < ε

end HigherDimLQGMetric
