import LQGDimension.Existence.AssemblyAux1
import LQGMetric.Statement.Metric
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Prob.Median
import LQGMetric.Field.WhiteNoise
import LQGMetric.Statement.Field
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Frozen definition: `segMeasure`

Anchor of the main theorem's constitutional surface (manifest `GaussianLQG/Frozen/frozen-anchors.json`).
Blueprint v3, Definition `def:segment`; source (1.5).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- The uniform probability measure on the segment `[z, w]` (blueprint Definition `def:segment`). -/
def segMeasure (z w : ℂ) : Measure ℂ :=
  (volume.restrict (Icc (0 : ℝ) 1)).map fun u : ℝ => ((1 - u : ℝ) : ℂ) * z + (u : ℂ) * w

end GaussianLQG
