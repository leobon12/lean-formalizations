import QuantumZipper.Proofs.Zipper.SWCoreNA2Core
import QuantumZipper.Proofs.GFF.CoordRegHarm
import QuantumZipper.Proofs.Zipper.SWCoreVAImg
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2: the deterministic log term, and the circle average of `x ∘ ψ + Q log|ψ'|`

Task SWC-NA (`handoff/SW-CORE.md` §5). For `ψ` holomorphic with `ψ' ≠ 0` on an open `U ⊇ B̄(z,r)`,
`r ≤ Im z`, the term `∫ log‖ψ'‖ dfc(z,r)` of `AreaDistClassGood` equals `log‖ψ'(z)‖`
(mean value property of the harmonic function `log|ψ'|`; mathlib
`AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` via `CoordReg.integral_log_norm_circleUnif_of_analytic`),
hence is continuous in the centre (`swcNA2_integral_log_deriv_fc`, `swcNA2_continuousAt_logterm`).
With the step-N0 identity `swcNA_avgReg_coordChange_eq` this gives
`avgReg (coordChange x ψ Q) k z − Q ∫ log‖ψ'‖ dfc(z, 2^{-k}) = evalReg x (ψ_* fc(z, 2^{-k}))` as
soon as `w ↦ evalReg x (ψ_* fc(w, 2^{-k}))` is continuous at `z` (`swcNA2_avgReg_coordChange_sub`),
which the family core provides almost surely. Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

/-- Mean value property of `log‖ψ'‖` on small circles. -/
theorem swcNA2_integral_log_deriv_fc {ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hψ : DifferentiableOn ℂ ψ U) (hne : ∀ u ∈ U, deriv ψ u ≠ 0) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hrz : r ≤ z.im) (hB : closedBall z r ⊆ U) :
    ∫ w, Real.log ‖deriv ψ w‖ ∂foldedCircle z r = Real.log ‖deriv ψ z‖ := by
  classical
  have hA : AnalyticOnNhd ℂ ψ U := hψ.analyticOnNhd hU
  set F : ℂ → ℂ := U.piecewise (deriv ψ) 1 with hF
  have hFeq : EqOn F (deriv ψ) U := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have hFm : Measurable F :=
    hA.deriv.continuousOn.measurable_piecewise continuous_const.continuousOn hU.measurableSet
  have hFa : AnalyticOnNhd ℂ F (closedBall z r) := fun u hu =>
    (hA.deriv u (hB hu)).congr (Filter.eventually_of_mem (hU.mem_nhds (hB hu))
      fun v hv => (hFeq hv).symm)
  have hF0 : ∀ u ∈ closedBall z r, F u ≠ 0 := fun u hu => by rw [hFeq (hB hu)]; exact hne u (hB hu)
  rw [foldedCircle_eq_circleUnif hr.le hrz]
  have h := CoordReg.integral_log_norm_circleUnif_of_analytic hFm hr.le hFa hF0
  rw [hFeq (hB (mem_closedBall_self hr.le))] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with u hu
  rw [hFeq (hB hu)]

end SWCore
end QuantumZipper
