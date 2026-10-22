import Mathlib.Analysis.Distribution.Distribution
import HigherDimLFPP.Frozen.Rd

/-!
# Frozen definition: `DistOn`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 61 ("a measurable map from distributions"), l. 67 (`h|_U`); [1] §1.2 (`𝒟'(ℝ^d)`): the
distributions on the open set `U` (mathlib's `Distribution U ℝ ⊤`, continuous linear functionals on `𝓓(U)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `𝒟'(U)`: mathlib's distributions on the open set `U ⊆ ℝ^d` (continuous linear functionals on
`𝓓(U)`). -/
abbrev DistOn {d : ℕ} (U : TopologicalSpace.Opens (Rd d)) : Type := 𝓓'(U, ℝ)

end HigherDimLQGMetric
