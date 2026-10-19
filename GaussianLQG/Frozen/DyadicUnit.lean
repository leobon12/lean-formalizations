import GaussianLQG.Frozen.SegMeasure

/-!
# Frozen definition: `dyadicUnit`

Anchor of the main theorem's constitutional surface (manifest `GaussianLQG/Frozen/frozen-anchors.json`).
Blueprint v3, Section `subsec:notation` (the dyadic rationals `𝔻` of `[0,1]`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- The dyadic rationals in `[0,1]`. -/
def dyadicUnit : Set ℝ := {y | ∃ n k : ℕ, k ≤ 2 ^ n ∧ y = (k : ℝ) / 2 ^ n}

end GaussianLQG
