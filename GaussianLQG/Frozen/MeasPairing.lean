import LQGDimension.Existence.AssemblyAux1
import LQGMetric.Statement.Metric
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Prob.Median
import LQGMetric.Field.WhiteNoise
import LQGMetric.Statement.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Frozen definition: `measPairing`

Anchor of the main theorem's constitutional surface (manifest `GaussianLQG/Frozen/frozen-anchors.json`).
Blueprint v3, Definition `def:pairing`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- `(g, μ) := lim_n ∫ ⟨g, ψ_{n,x}⟩ dμ(x)`, the pairing of a distribution with a measure through
the mollified field `x ↦ ⟨g, ψ_{n,x}⟩` at scale `2^{-n}` (blueprint Definition `def:pairing`). Where
the limit does not exist, `limUnder` returns an unspecified value; for the GFF this happens only on a
null set. For circle measures this is `LQGMetric.circleAvg`. -/
def measPairing (g : LQGMetric.DistC) (μ : Measure ℂ) : ℝ :=
  limUnder atTop fun n : ℕ => ∫ x, g (LQGMetric.bumpTest n x) ∂μ

end GaussianLQG
