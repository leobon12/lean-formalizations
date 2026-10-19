import HigherDimLFPP.Frozen.Rd

/-!
# Frozen definition: `e₁`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1: `e₁ = (1, 0, …, 0)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPP

/-- `e₁ = (1, 0, …, 0)`. -/
def e₁ (d : ℕ) : Rd d := WithLp.toLp 2 (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0)

end HigherDimLFPP
