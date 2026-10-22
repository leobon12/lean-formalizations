import HigherDimLQGMetric.DGZ.NondegLambdaComparable
import HigherDimLQGMetric.DGZ.TightExports
import HigherDimLQGMetric.DGZ.Adapter

/-! Unconditional DGZ exports for the real-cutoff weak-metric adapter. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

theorem realEpsAdapterShape (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ) :
    RealEpsAdapterShape d κ ξ Q :=
  realEpsAdapter d κ ξ Q
    (holderTightShape_of_lambdaComparable (lambdaComparableShape d κ ξ Q))
    (nondegShape d κ ξ Q) (distInfShape d κ ξ Q)

end HigherDimLQGMetric.DGZ
