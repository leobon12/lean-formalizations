import GaussianLQG.Frozen.SegPairing
import GaussianLQG.Frozen.DyadicUnit

/-!
# Frozen definition: `diagMin`

Anchor of the main theorem's constitutional surface (manifest `GaussianLQG/Frozen/frozen-anchors.json`).
Blueprint v3, Definition `def:HMq`; source (1.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- `M = min_{y ∈ [0,1]} H(y,y)`, written as an infimum over dyadic `y` (blueprint Definition
`def:HMq`). -/
def diagMin (h : LQGMetric.DistC) : ℝ := ⨅ y : dyadicUnit, segPairing h y y

end GaussianLQG
