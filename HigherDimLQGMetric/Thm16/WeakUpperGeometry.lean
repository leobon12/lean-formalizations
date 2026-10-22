import HigherDimLQGMetric.Sharp.TightWeak
import HigherDimLQGMetric.Sharp.W2Det

/-! A good scaled sphere gives a physical internal-distance upper bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_internal_le_scaledSphereDiam {d : ℕ}
    (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (h : DistRd d) {r M : ℝ} (hr : 0 < r) (hc : 0 < c r)
    (hM : 0 ≤ M)
    (hgood : sphereDiam (weakScaledMetric ξ D c h hr 0 hc) 0 1 ≤ ENNReal.ofReal M)
    {U : Set (Rd d)} (hU : ann (0 : Rd d) (r / 2) (2 * r) ⊆ U)
    {z w : Rd d} (hz : z ∈ sphere (0 : Rd d) r)
    (hw : w ∈ sphere (0 : Rd d) r) :
    (D h).internal U z w ≤
      ENNReal.ofReal (c r * Real.exp (ξ * sphereAvg h r 0) * M) := by
  let a : ℝ := c r * Real.exp (ξ * sphereAvg h r 0)
  have ha : 0 < a := mul_pos hc (Real.exp_pos _)
  let q : ℝ≥0∞ := ENNReal.ofReal a
  let qi : ℝ≥0∞ := ENNReal.ofReal a⁻¹
  have hqi : q * qi = 1 := by
    dsimp [q, qi]
    rw [← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ ha.ne', ENNReal.ofReal_one]
  have hfac : (c r)⁻¹ * Real.exp (-ξ * sphereAvg h r 0) = a⁻¹ := by
    dsimp [a]
    rw [show -ξ * sphereAvg h r 0 = -(ξ * sphereAvg h r 0) by ring,
      Real.exp_neg, mul_inv_rev]
    ring
  have hscaled : qi * sphereDiam (D h) 0 r ≤ ENNReal.ofReal M := by
    rw [weakScaledMetric_sphereDiam, hfac] at hgood
    exact hgood
  have hdiam : sphereDiam (D h) 0 r ≤ ENNReal.ofReal (M * a) := by
    calc
      sphereDiam (D h) 0 r = q * (qi * sphereDiam (D h) 0 r) := by
        rw [← mul_assoc, hqi, one_mul]
      _ ≤ q * ENNReal.ofReal M := by
        simpa only [mul_comm] using (mul_le_mul_left hscaled q)
      _ = ENNReal.ofReal (M * a) := by
        rw [ENNReal.ofReal_mul hM]
        exact mul_comm _ _
  have hint := w2_internal_le_sphereDiam (D h) U 0 r hU hz hw
  calc
    (D h).internal U z w ≤ sphereDiam (D h) 0 r := hint
    _ ≤ ENNReal.ofReal (M * a) := hdiam
    _ = ENNReal.ofReal (c r * Real.exp (ξ * sphereAvg h r 0) * M) := by
      congr 1
      dsimp [a]
      ring

end HigherDimLQGMetric
