import HigherDimLFPP.Frozen.Rd
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frozen definition: `scaleKernel`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1: `K_t(z) = t^{-(d+1)/2} κ(z/t)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPP

/-- `K_t(z) = t^{-(d+1)/2} κ(z/t)`. -/
def scaleKernel {d : ℕ} (κ : Rd d → ℝ) (t : ℝ) (z : Rd d) : ℝ :=
  t ^ (-((d : ℝ) + 1) / 2) * κ (t⁻¹ • z)

end HigherDimLFPP
