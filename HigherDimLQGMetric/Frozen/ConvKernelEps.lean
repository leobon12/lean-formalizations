import HigherDimLQGMetric.Frozen.ConvKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frozen definition: `convKernelEps`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[1] §1.1 (before (1.2)): `K_ε(x) = ε^{-d} K(x/ε)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `K_ε(x) = ε^{-d} K(x/ε)`. -/
def convKernelEps {d : ℕ} (κ : Rd d → ℝ) (ε : ℝ) (x : Rd d) : ℝ :=
  ε ^ (-(d : ℝ)) * convKernel κ (ε⁻¹ • x)

end HigherDimLQGMetric
