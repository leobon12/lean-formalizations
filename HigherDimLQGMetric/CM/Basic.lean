import HigherDimLQGMetric.LogEnergy.CM
import HigherDimLQGMetric.Sphere.Avg

/-!
# Mean-zero pairings and normalized Cameron–Martin shifts

The field is represented by a distribution; mean-zero pairings forget its additive constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The mean-zero pairings of a distribution on `ℝ^d`. -/
def pair0Rd (g : DistRd d) : TestRd0 d → ℝ := fun φ => g φ.1

/-- Add a continuous function and return to the unit-sphere normalization. -/
def shiftNorm (g : DistRd d) (F : C(Rd d, ℝ)) : DistRd d :=
  addConst (addFun g F) (-(∫ u, F u ∂(unitSphereProb d)))

end HigherDimLQGMetric
