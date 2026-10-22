import HigherDimLQGMetric.Frozen.DistOn

/-!
# Frozen definition: `DistRd`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 61: `𝒟'(ℝ^d) = 𝒟'(⊤)`, the domain of a metric assignment; its σ-algebra is the cylinder
σ-algebra `DistOn.measurableSpace ⊤`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `𝒟'(ℝ^d)`: distributions on the whole space. -/
abbrev DistRd (d : ℕ) : Type := DistOn (⊤ : TopologicalSpace.Opens (Rd d))

end HigherDimLQGMetric
