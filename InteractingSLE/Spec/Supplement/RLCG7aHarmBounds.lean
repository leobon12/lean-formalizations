/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Local domination of nonnegative harmonic functions

Packet PROVE-G7A-MEANIDENT. The disk Poisson formula and Mathlib's
Herglotz--Riesz kernel bound give an integrable dominating section for a
family of nonnegative harmonic functions.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Complex InnerProductSpace

namespace InteractingSLE.Restart.FlowLocalityGen

/-- A nonnegative harmonic function on a closed disk is bounded by three
times its value at the center on the disk of half the radius. -/
theorem nonneg_harmonic_le_three_mul_center {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : HarmonicOnNhd f (closedBall c R))
    (hf0 : ∀ z ∈ closedBall c R, 0 ≤ f z) (hw : w ∈ closedBall c (R / 2)) :
    f w ≤ 3 * f c := by
  have hwR : w ∈ ball c R := closedBall_subset_ball (by linarith) hw
  have hwN : ‖w - c‖ ≤ R / 2 := mem_closedBall_iff_norm.1 hw
  have hden : 0 < R - ‖w - c‖ := by linarith
  have hratio : (R + ‖w - c‖) / (R - ‖w - c‖) ≤ 3 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hsph : sphere c |R| ⊆ closedBall c R := by
    rw [abs_of_pos hR]
    exact sphere_subset_closedBall
  have hP : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    unfold poissonKernel
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro z hz
    have hzN : ‖z - c‖ = R := by
      simpa only [abs_of_pos hR, mem_sphere_iff_norm] using hz
    have hne : z - c - (w - c) ≠ 0 := by
      intro he
      have : z = w := by linear_combination he
      subst z
      linarith
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hne)
  have hfc : ContinuousOn f (sphere c |R|) := hf.continuousOn.mono hsph
  have hPi : CircleIntegrable (poissonKernel c w • f) c R :=
    (hP.smul hfc).circleIntegrable'
  have h3i : CircleIntegrable (fun z => (3 : ℝ) * f z) c R :=
    (continuousOn_const.mul hfc).circleIntegrable'
  calc
    f w = Real.circleAverage (poissonKernel c w • f) c R :=
      (hf.circleAverage_poissonKernel_smul hwR).symm
    _ ≤ Real.circleAverage (fun z => (3 : ℝ) * f z) c R := by
      refine Real.circleAverage_mono hPi h3i fun z hz => ?_
      have hzR : z ∈ sphere c R := by simpa only [abs_of_pos hR] using hz
      have hkernel : poissonKernel c w z ≤ 3 := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]
        exact (re_herglotzRieszKernel_le hzR hwR).trans hratio
      exact mul_le_mul_of_nonneg_right hkernel (hf0 z (hsph hz))
    _ = 3 * f c := by
      change Real.circleAverage (fun z => (3 : ℝ) • f z) c R = (3 : ℝ) • f c
      have hf' : HarmonicOnNhd f (closedBall c |R|) := by
        simpa only [abs_of_pos hR] using hf
      rw [Real.circleAverage_fun_smul, hf'.circleAverage_eq]

end InteractingSLE.Restart.FlowLocalityGen
