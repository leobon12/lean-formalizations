import HigherDimLFPP.Frozen.Rd

/-!
# Frozen definition: `IsMetricFn`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 60–61 ("All metrics ... are finite"): `D` is a finite metric on `ℝ^d`, written as a function on
`ℝ^d × ℝ^d` (field names and bodies identical to MA0 Details (c) and MA7 Details (c) §F).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `D` is a (finite) metric on `ℝ^d`, written as a function on `ℝ^d × ℝ^d`. -/
structure IsMetricFn {d : ℕ} (D : Rd d × Rd d → ℝ) : Prop where
  self_eq_zero : ∀ x, D (x, x) = 0
  eq_of_eq_zero : ∀ x y, D (x, y) = 0 → x = y
  symm : ∀ x y, D (x, y) = D (y, x)
  triangle : ∀ x y z, D (x, z) ≤ D (x, y) + D (y, z)

end HigherDimLQGMetric
