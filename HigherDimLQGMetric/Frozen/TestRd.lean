import HigherDimLQGMetric.Frozen.TestOn

/-!
# Frozen definition: `TestRd`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 51–55 (test functions on `ℝ^d`): `𝓓(ℝ^d) = 𝓓(⊤)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `𝓓(ℝ^d)`: test functions on the whole space. -/
abbrev TestRd (d : ℕ) : Type := TestOn (⊤ : TopologicalSpace.Opens (Rd d))

end HigherDimLQGMetric
