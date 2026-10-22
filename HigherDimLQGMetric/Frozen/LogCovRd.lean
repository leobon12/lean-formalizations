import HigherDimLFPP.Frozen.Rd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Frozen definition: `logCovRd`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 52–56, [1] (1.1): the LGF covariance `∫∫ φ(x) log(1/|x - y|) ψ(y) dx dy` (finite for test
functions: the logarithmic singularity is locally integrable).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `∫∫ φ(x) log(1/|x - y|) ψ(y) dx dy`. -/
def logCovRd {d : ℕ} (φ ψ : Rd d → ℝ) : ℝ := ∫ x, ∫ y, φ x * (-Real.log ‖x - y‖) * ψ y

end HigherDimLQGMetric
