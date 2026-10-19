import GaussianLQG.Frozen.SegMeasure
import GaussianLQG.Frozen.MeasPairing

/-!
# Frozen definition: `segPairing`

Anchor of the main theorem's constitutional surface (manifest `GaussianLQG/Frozen/frozen-anchors.json`).
Blueprint v3, Definition `def:HMq`; source (1.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- `H(s,t) = (h, λ_{is, 1+it})`: the average of the field along the segment from `is` to `1+it`
(blueprint Definition `def:HMq`; source (1.6)). -/
def segPairing (h : LQGMetric.DistC) (s t : ℝ) : ℝ :=
  measPairing h (segMeasure ((s : ℂ) * Complex.I) (1 + (t : ℂ) * Complex.I))

end GaussianLQG
