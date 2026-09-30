import QuantumZipper.Proofs.Zipper.SWCoreA5Dens
import QuantumZipper.Proofs.Zipper.SWCoreNA2Log
import QuantumZipper.Proofs.LQG.RegularClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A7 (1): the pushed average of `x ∘ ψ + Q log|ψ'|` from the pushed `evalReg`

Deterministic identity used to read the finite-parameter primed area core `swcNA2I_primed`
(decision D64) in the `pushErr` form of SWC-A5/A6: if the pushed regularized value
`s ↦ evalReg x ((fc(s, 2^{-k})).map ψ)` is continuous at `z` along the dyadic centres, then,
by the mean value property of the harmonic function `log‖ψ'‖` (`swcNA2_integral_log_deriv_fc`),

  `avgReg (coordChange x ψ Q) k z = evalReg x ((fc(z,2^{-k})).map ψ) + Q log‖ψ'(z)‖`,

so `pushErr` is exactly the difference of the pushed and the round regularized values.
Own bookkeeping (Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7)).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

/-- Eventually the dyadic centres of `z` carry circles of radius `r` inside `closedBall z (2r)`
and below height `Im z - r`. -/
theorem a7_dyadic_small {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, closedBall (dyadicRoundC n z) r ⊆ closedBall z (2 * r) ∧
      z.im - r ≤ (dyadicRoundC n z).im := by
  have h := (RegClosure.tendsto_dyadicRoundC z).eventually (closedBall_mem_nhds z hr)
  filter_upwards [h] with n hn
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w (dyadicRoundC n z) z]
  · have h1 := Complex.abs_im_le_norm (dyadicRoundC n z - z)
    rw [← dist_eq_norm, Complex.sub_im] at h1
    linarith [(abs_le.1 (h1.trans hn)).1]

/-- **The pushed average identity.** -/
theorem a7_avgReg_eq {x : FieldSample} {ψ : ℂ → ℂ} {Q : ℝ} {k : ℕ} {z : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) (hne : ∀ u ∈ U, deriv ψ u ≠ 0)
    (hB : closedBall z (2 * radius k) ⊆ U) (him : 2 * radius k ≤ z.im)
    (h1 : Tendsto (fun n => evalReg x ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ))
      atTop (𝓝 (evalReg x ((foldedCircle z (radius k)).map ψ)))) :
    avgReg (coordChange x ψ Q) k z =
      evalReg x ((foldedCircle z (radius k)).map ψ) + Q * Real.log ‖deriv ψ z‖ := by
  have hr := radius_pos k
  have hzU : z ∈ U := hB (mem_closedBall_self (by positivity))
  have hA : AnalyticOnNhd ℂ ψ U := hψ.analyticOnNhd hU
  have hdc : ContinuousAt (fun w => Real.log ‖deriv ψ w‖) z :=
    ((hA.deriv z hzU).continuousAt.norm).log (norm_ne_zero_iff.2 (hne z hzU))
  have hlim : Tendsto (fun n => Real.log ‖deriv ψ (dyadicRoundC n z)‖) atTop
      (𝓝 (Real.log ‖deriv ψ z‖)) := hdc.tendsto.comp (RegClosure.tendsto_dyadicRoundC z)
  have heq : ∀ᶠ n in atTop, coordChange x ψ Q (foldedCircle (dyadicRoundC n z) (radius k)) =
      evalReg x ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ) +
        Q * Real.log ‖deriv ψ (dyadicRoundC n z)‖ := by
    filter_upwards [a7_dyadic_small hr] with n hn
    unfold coordChange
    rw [swcNA2_integral_log_deriv_fc hU hψ hne hr (by linarith [hn.2]) (hn.1.trans hB)]
  unfold avgReg
  refine Tendsto.limUnder_eq ?_
  exact (h1.add (hlim.const_mul Q)).congr' (heq.mono fun n hn => hn.symm)

/-- **`pushErr` is the difference of the pushed and the round regularized values.** -/
theorem a7_pushErr_eq {γ : ℝ} {x : FieldSample} {ψ : ℂ → ℂ} {k : ℕ} {z : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) (hne : ∀ u ∈ U, deriv ψ u ≠ 0)
    (hB : closedBall z (2 * radius k) ⊆ U) (him : 2 * radius k ≤ z.im)
    (h1 : Tendsto (fun n => evalReg x ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ))
      atTop (𝓝 (evalReg x ((foldedCircle z (radius k)).map ψ)))) :
    pushErr γ x ψ k z = evalReg x ((foldedCircle z (radius k)).map ψ) -
      evalReg x (foldedCircle (ψ z) (radius k * ‖deriv ψ z‖)) := by
  unfold pushErr
  rw [a7_avgReg_eq hU hψ hne hB him h1]
  ring

end SWCore
end QuantumZipper
