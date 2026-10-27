import Mathlib
import LQGMetric.Statement.GFF

/-!
# Frozen definition: `MatedCRT.Field`

An `abbrev`. The host modules `LQGMetric.Statement.GFF` and `LQGMetric.Statement.Field` are imported, not copied,
and pinned in the manifest (`upstream.modules`; (1)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Real distributions on `ℂ` (LQGMetric's `DistC`, mathlib `𝓓'(ℂ, ℝ)` with the cylinder σ-algebra). -/
abbrev Field := LQGMetric.DistC

end MatedCRT

end MatedCRTHarmonic
