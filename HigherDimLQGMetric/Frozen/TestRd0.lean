import HigherDimLQGMetric.Frozen.TestRd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Frozen definition: `TestRd0`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 52–56 ("∫ϕ = ∫ψ = 0"), [1] (1.1): test functions with zero mean (they see the LGF modulo
constants).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Mean-zero test functions on `ℝ^d`. -/
def TestRd0 (d : ℕ) : Type := {φ : TestRd d // ∫ z, φ z = 0}

end HigherDimLQGMetric
