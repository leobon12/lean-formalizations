import HigherDimLQGMetric.Frozen.IsContinuousMetric

/-!
# Frozen definition: `ContMetric`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 60–62 ("A metric assignment is a measurable map from distributions to such metrics"), [1] §1.2:
the space of continuous metrics on `ℝ^d` inducing the Euclidean topology, a subspace of `C(ℝ^d × ℝ^d, ℝ)`
(compact-open = local uniform topology; its Borel σ-algebra via mathlib's subtype instances).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The space of continuous metrics on `ℝ^d` inducing the Euclidean topology (local uniform topology,
Borel σ-algebra, through the subtype instances). -/
abbrev ContMetric (d : ℕ) : Type := {D : C(Rd d × Rd d, ℝ) // IsContinuousMetric D}

end HigherDimLQGMetric
