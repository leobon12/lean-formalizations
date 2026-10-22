import HigherDimLQGMetric.Core.Defs
import HigherDimLQGMetric.Sphere.Var
import GaussianLQG.Probability.Gaussian

/-!
# The scale lattice and macroscopic normalizer

The deterministic objects in the global scale-bin estimate, in the exact source convention.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The scale lattice `𝒮 = {64^j : j ∈ ℤ}`. -/
def scaleLattice : Set ℝ := {r | ∃ j : ℤ, r = (64 : ℝ) ^ j}

/-- `S = R^{ξQ} e^{ξ h_{8R}(0)}` from equation (24). -/
def macroS {d : ℕ} (ξ Q : ℝ) (h : DistRd d) (R : ℝ) : ℝ :=
  R ^ (ξ * Q) * Real.exp (ξ * sphereAvg h (8 * R) 0)

end HigherDimLQGMetric
