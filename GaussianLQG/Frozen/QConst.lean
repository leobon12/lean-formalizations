import GaussianLQG.Frozen.DiagMin
import LQGMetric.Statement.LFPP

/-!
# Frozen definition: `qConst`

Anchor of the main theorem's constitutional surface (manifest `GaussianLQG/Frozen/frozen-anchors.json`).
Blueprint v3, Definition `def:HMq`; source (1.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- `q = med M`, the lower median of `M` under the law of the normalized whole-plane GFF. -/
def qConst : ℝ := LQGMetric.lowerMedian LQGMetric.normGFFLaw diagMin

end GaussianLQG
