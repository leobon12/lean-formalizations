/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aHarmBounds
import Mathlib.MeasureTheory.Integral.Prod
import QuantumZipper.Proofs.GFF.K3.HarmonicPart

/-!
# Passing the harmonic mean-value identity through an integral

Packet PROVE-G7A-MEANIDENT. Under a common integrable bound, Carathéodory
measurability and Fubini transfer the circle mean-value identity from the
harmonic sections to their integral.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Complex InnerProductSpace

namespace InteractingSLE.Restart.FlowLocalityGen

/-- Fubini transfers the circle mean-value identity under an integrable bound. -/
theorem circleAverage_integral_eq_of_bound {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {U : Set ℂ} {k : A → ℂ → ℝ} {b : A → ℝ}
    (hk : ∀ a, HarmonicOnNhd (k a) U)
    (hm : ∀ z ∈ U, Measurable (fun a => k a z)) (hb : Integrable b μ)
    (hbound : ∀ a, ∀ z ∈ U, ‖k a z‖ ≤ b a)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (hball : closedBall c R ⊆ U) :
    Real.circleAverage (fun z => ∫ a, k a z ∂μ) c R = ∫ a, k a c ∂μ := by
  have hcm : ∀ θ : ℝ, circleMap c R θ ∈ U := fun θ =>
    hball (sphere_subset_closedBall (circleMap_mem_sphere c hR θ))
  have hc : ∀ a, Continuous (fun θ => k a (circleMap c R θ)) := fun a =>
    (hk a).continuousOn.comp_continuous (continuous_circleMap c R) hcm
  have hmeas : Measurable (fun p : ℝ × A => k p.2 (circleMap c R p.1)) :=
    measurable_uncurry_of_continuous_of_measurable hc (fun θ => hm _ (hcm θ))
  have hi : Integrable (fun p : ℝ × A => k p.2 (circleMap c R p.1))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod μ) := by
    refine (hb.comp_snd (volume.restrict (Ioc 0 (2 * Real.pi)))).mono'
      hmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    exact hbound p.2 _ (hcm p.1)
  calc
    Real.circleAverage (fun z => ∫ a, k a z ∂μ) c R =
        (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), ∫ a, k a (circleMap c R θ) ∂μ := by
      rw [Real.circleAverage_def, smul_eq_mul,
        intervalIntegral.integral_of_le Real.two_pi_pos.le]
    _ = (2 * Real.pi)⁻¹ * ∫ a, (∫ θ in Ioc 0 (2 * Real.pi), k a (circleMap c R θ)) ∂μ := by
      rw [integral_integral_swap hi]
    _ = ∫ a, Real.circleAverage (k a) c R ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun a => by
        dsimp only
        rw [Real.circleAverage_def, smul_eq_mul,
          intervalIntegral.integral_of_le Real.two_pi_pos.le]
    _ = ∫ a, k a c ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun a => ?_)
      exact ((hk a).mono (by simpa only [abs_of_nonneg hR] using hball)).circleAverage_eq

end InteractingSLE.Restart.FlowLocalityGen
