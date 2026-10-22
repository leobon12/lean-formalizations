import HigherDimLQGMetric.B3.Interfaces
import HigherDimLFPP.Paths.Compare

/-!
# Exact similarity covariance of convolution LFPP distances

This deterministic bridge isolates the path-metric calculation in MA5 A8.
The stochastic scaling of the convolution field is supplied separately by the
LGF law and the radial convolution identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- If the convolution fields match after a similarity up to a constant, the
whole-space LFPP distances match with the exact Euclidean and Weyl factors. -/
theorem l6a_lfppDist_scale_of_conv_eq {d : ℕ} (κ : Rd d → ℝ)
    (ξ ε ρ c : ℝ) (hρ : 0 < ρ) (h g : DistRd d) (x₀ u v : Rd d)
    (heq : ∀ z : Rd d, convMollify κ ε h (x₀ + ρ • z) =
      convMollify κ (ε / ρ) g z + c) :
    lfppDist κ ξ ε h (x₀ + ρ • u, x₀ + ρ • v) =
      ρ * Real.exp (ξ * c) * lfppDist κ ξ (ε / ρ) g (u, v) := by
  rw [lfppDist]
  rw [HigherDimLFPP.lfppDistOn_translate x₀ ξ (convMollify κ ε h) univ
    (ρ • u) (ρ • v)]
  simp only [Set.preimage_univ]
  rw [HigherDimLFPP.lfppDistOn_smul hρ ξ
    (fun z => convMollify κ ε h (x₀ + z)) univ u v]
  simp only [Set.preimage_univ]
  have hfield : (fun z : Rd d => convMollify κ ε h (x₀ + ρ • z)) =
      fun z => convMollify κ (ε / ρ) g z + c := funext heq
  rw [hfield, HigherDimLFPP.lfppDistOn_add_const]
  simp only [lfppDist]
  ring

end HigherDimLQGMetric
