import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Frozen definition: `Rd`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1 (ℝ^d with the Euclidean norm).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPP

/-- `ℝ^d` with the Euclidean norm and its Lebesgue measure.  (Not `Fin d → ℝ`, which carries the
sup norm.) -/
abbrev Rd (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

end HigherDimLFPP
