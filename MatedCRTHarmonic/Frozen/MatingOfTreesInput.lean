import Mathlib
import MatedCRTHarmonic.Frozen.MatedCRTPath2
import MatedCRTHarmonic.Frozen.MatedCRTField
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Frozen definition: `MatedCRT.MatingOfTreesInput`

A mating-of-trees coupling on a standard Borel probability space, as in `CellModelExists`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **A mating-of-trees coupling** : for `γ`, a mating-of-trees coupling exists on a
standard Borel probability space. The coupling records the field, curve, and Brownian motion data used in [18]. -/
def MatingOfTreesInput (γ : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
    (X X₀ hIG₀ : Ω → Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → Path2),
    IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm

end MatedCRT

end MatedCRTHarmonic
