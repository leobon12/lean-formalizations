import HigherDimLQGContinuity.Caps.Grid
import HigherDimLQGContinuity.Param.Lipschitz

/-!
# Deterministic scale-ratio cap (packet P4)

On an inspected grid point, a cap on the sphere average gives the parameter
Lipschitz estimate for the physical scaling factors, including parameter zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Lemma 2.2(b), pointwise: the cap and `ϕ`-Lipschitz estimate control the
ratio of scaling factors, including at `ξ=0` and `η=0`. -/
theorem scale_ratio_cap {d : ℕ} (hd : 2 ≤ d) (g : DistRd d) (z : Rd d)
    {s r n C ξ η : ℝ} (hξ : 0 ≤ ξ) (hη : 0 ≤ η)
    (hr : 0 < r) (hr1 : r ≤ 1) (hlog : -Real.log r ≤ n)
    (hcap : |sphereAvg g (s * r) z| ≤ C * n) (_hn : 0 ≤ n) (_hC : 0 ≤ C) :
    |Real.log (scaleS d η s r z g / scaleS d ξ s r z g)| ≤
      (Real.sqrt (2 * d) + C) * |η - ξ| * n := by
  rw [scaleS_ratio d ξ η s hr, Real.log_exp]
  have hφ := phiXi_lipschitz_nonneg hd hη hξ
  have hlog0 : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
  have hlogabs : |Real.log r| ≤ n := by rw [abs_of_nonpos hlog0]; exact hlog
  have hsq : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
  have hdiff : 0 ≤ |η - ξ| := abs_nonneg _
  calc
    |(phiXi d η - phiXi d ξ) * Real.log r +
        (η - ξ) * sphereAvg g (s * r) z|
        ≤ |phiXi d η - phiXi d ξ| * |Real.log r| +
          |η - ξ| * |sphereAvg g (s * r) z| := by
            simpa only [abs_mul] using abs_add_le
              ((phiXi d η - phiXi d ξ) * Real.log r)
              ((η - ξ) * sphereAvg g (s * r) z)
    _ ≤ (Real.sqrt (2 * d) + C) * |η - ξ| * n := by
      calc
        _ ≤ (Real.sqrt (2 * d) * |η - ξ|) * n +
              |η - ξ| * (C * n) := by
                gcongr
        _ = _ := by ring

end HigherDimLQGContinuity
