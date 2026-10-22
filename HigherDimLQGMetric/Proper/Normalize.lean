import HigherDimLQGMetric.Proper.Bounds
import HigherDimLQGMetric.Core.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Algebra of the sharp scale normalizer

The bounds from weak tightness are for normalized distances. These identities restore the
unnormalized metric and compare two scales.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A normalized metric value times its sharp normalizer is the original distance. -/
theorem proper_normalized_mul (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (h : DistRd d) {r : ℝ} (hr : 0 < r) (u v : Rd d) :
    sNorm ξ Q h r 0 *
        normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) h r (u, v) =
      (D h).1 (r • u, r • v) := by
  change (r ^ (ξ * Q) * Real.exp (ξ * sphereAvg h r 0)) *
      ((r ^ (ξ * Q))⁻¹ * Real.exp (-ξ * sphereAvg h r 0) *
        (D h).1 (r • u, r • v)) = _
  have hp : r ^ (ξ * Q) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have he : Real.exp (ξ * sphereAvg h r 0) *
      Real.exp (-ξ * sphereAvg h r 0) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ = ((r ^ (ξ * Q)) * (r ^ (ξ * Q))⁻¹) *
          (Real.exp (ξ * sphereAvg h r 0) *
            Real.exp (-ξ * sphereAvg h r 0)) * (D h).1 (r • u, r • v) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hp, he, one_mul, one_mul]

/-- Sharp normalizer at radius `e^n R`, expressed relative to radius `R`. -/
theorem proper_sNorm_exp_mul (ξ Q : ℝ) (h : DistRd d) {R : ℝ} (hR : 0 < R)
    (n : ℝ) :
    sNorm ξ Q h (Real.exp n * R) 0 =
      sNorm ξ Q h R 0 *
        Real.exp (ξ * Q * n + ξ *
          (sphereAvg h (Real.exp n * R) 0 - sphereAvg h R 0)) := by
  have he : 0 < Real.exp n := Real.exp_pos _
  have heR : 0 < Real.exp n * R := mul_pos he hR
  change (Real.exp n * R) ^ (ξ * Q) *
      Real.exp (ξ * sphereAvg h (Real.exp n * R) 0) =
    R ^ (ξ * Q) * Real.exp (ξ * sphereAvg h R 0) *
      Real.exp (ξ * Q * n + ξ *
        (sphereAvg h (Real.exp n * R) 0 - sphereAvg h R 0))
  rw [Real.rpow_def_of_pos heR, Real.rpow_def_of_pos hR,
    Real.log_mul he.ne' hR.ne', Real.log_exp]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end HigherDimLQGMetric
