import HigherDimLQGMetric.Amplify.Normalizer

/-! Exact recentering and Gaussian-window bounds for the scale normalizer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The trial normalizer differs from the outer one by one spherical-average
increment and the deterministic power of the scale ratio. -/
theorem amplify_sNorm_ratio (ξ Q : ℝ) (H : DistRd d)
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (w : Rd d) :
    sNorm ξ Q H (ρ * r) (r • w) =
      ρ ^ (ξ * Q) *
        Real.exp (ξ * (sphereAvg H (ρ * r) (r • w) - sphereAvg H r 0)) *
          sNorm ξ Q H r 0 := by
  let a := sphereAvg H (ρ * r) (r • w)
  let b := sphereAvg H r 0
  have hpow : (ρ * r) ^ (ξ * Q) = ρ ^ (ξ * Q) * r ^ (ξ * Q) :=
    Real.mul_rpow hρ.le hr.le
  have hexp : Real.exp (ξ * a) = Real.exp (ξ * (a - b)) * Real.exp (ξ * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold sNorm
  rw [hpow, hexp]
  ring

/-- A uniform bound for the Gaussian increment becomes a two-sided
deterministic bound on every selected trial normalizer. -/
theorem amplify_sNorm_ratio_bounds {ξ Q : ℝ} (hξ : 0 < ξ)
    (H : DistRd d) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (w : Rd d) {K : ℝ}
    (hK : |sphereAvg H (ρ * r) (r • w) - sphereAvg H r 0| ≤ K) :
    ρ ^ (ξ * Q) * Real.exp (-ξ * K) * sNorm ξ Q H r 0 ≤
      sNorm ξ Q H (ρ * r) (r • w) ∧
    sNorm ξ Q H (ρ * r) (r • w) ≤
      ρ ^ (ξ * Q) * Real.exp (ξ * K) * sNorm ξ Q H r 0 := by
  let Z := sphereAvg H (ρ * r) (r • w) - sphereAvg H r 0
  have hZ := abs_le.mp hK
  have hLo : Real.exp (-ξ * K) ≤ Real.exp (ξ * Z) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hξ.le (sub_nonneg.mpr hZ.1)]
  have hHi : Real.exp (ξ * Z) ≤ Real.exp (ξ * K) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hξ.le (sub_nonneg.mpr hZ.2)]
  have hsn : 0 ≤ sNorm ξ Q H r 0 := by unfold sNorm; positivity
  rw [amplify_sNorm_ratio ξ Q H hρ hr w]
  constructor
  · gcongr
  · gcongr

end HigherDimLQGMetric
