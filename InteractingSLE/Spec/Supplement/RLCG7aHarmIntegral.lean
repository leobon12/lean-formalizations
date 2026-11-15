/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aHarmMean
import Mathlib.Topology.TietzeExtension
import QuantumZipper.Proofs.GFF.CoordRegHarm

/-!
# Integrals of nonnegative harmonic sections

Packet PROVE-G7A-MEANIDENT. The local Poisson bound provides domination by
the integrable section at the center. Dominated convergence gives continuity;
Fubini gives the mean-value identity; QuantumZipper's Weyl lemma gives
harmonicity. This module treats measurable parameter sections. The completion
adapter in the next module removes that extra measurability requirement.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Complex InnerProductSpace Filter Topology

namespace InteractingSLE.Restart.FlowLocalityGen

/-- Integration preserves nonnegative harmonic sections when the parameter
sections are measurable and integrable. -/
theorem harmonicOnNhd_integral_nonneg_of_measurable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {U : Set ℂ} (hU : IsOpen U) {k : A → ℂ → ℝ}
    (hk : ∀ a, HarmonicOnNhd (k a) U) (h0 : ∀ a, ∀ z ∈ U, 0 ≤ k a z)
    (hi : ∀ z ∈ U, Integrable (fun a => k a z) μ)
    (hm : ∀ z ∈ U, Measurable (fun a => k a z)) :
    HarmonicOnNhd (fun z => ∫ a, k a z ∂μ) U := by
  intro c hc
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU c hc
  let r : ℝ := ε / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have hlarge : closedBall c (2 * r) ⊆ U :=
    (closedBall_subset_ball (by dsimp only [r]; linarith)).trans hεU
  have hsmall : closedBall c r ⊆ U :=
    (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)).trans hlarge
  have hb : Integrable (fun a => 3 * k a c) μ := (hi c hc).const_mul 3
  have hbound : ∀ a, ∀ z ∈ closedBall c r, ‖k a z‖ ≤ 3 * k a c := by
    intro a z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 a z (hsmall hz))]
    exact nonneg_harmonic_le_three_mul_center (by linarith : 0 < 2 * r)
      ((hk a).mono hlarge) (fun z hz => h0 a z (hlarge hz))
      (mem_closedBall_iff_norm.2 (by have := mem_closedBall_iff_norm.1 hz; linarith))
  have hcont : ContinuousOn (fun z => ∫ a, k a z ∂μ) (closedBall c r) := by
    exact continuousOn_of_dominated (fun z hz => (hi z (hsmall hz)).aestronglyMeasurable)
      (fun z hz => ae_of_all _ fun a => hbound a z hz) hb
      (ae_of_all _ fun a => (hk a).continuousOn.mono hsmall)
  let fK : C(closedBall c r, ℝ) := ⟨fun z => ∫ a, k a z ∂μ, hcont.domRestrict⟩
  obtain ⟨g, hg⟩ := fK.exists_restrict_eq isClosed_closedBall
  have heq : EqOn g (fun z => ∫ a, k a z ∂μ) (closedBall c r) := by
    intro z hz
    exact congrArg (fun f : C(closedBall c r, ℝ) => f ⟨z, hz⟩) hg
  have hV : ball c r ⊆ U := ball_subset_closedBall.trans hsmall
  have hmean : QuantumZipper.K3.MeanValueOn g (ball c r) := by
    intro y hy s hs hB
    have hcircle : EqOn g (fun z => ∫ a, k a z ∂μ) (sphere y |s|) := by
      intro z hz
      apply heq
      apply ball_subset_closedBall
      apply hB
      exact sphere_subset_closedBall (by simpa only [abs_of_pos hs] using hz)
    rw [QuantumZipper.CoordReg.integral_circleUnif_eq_circleAverage g.continuous.measurable,
      Real.circleAverage_congr_sphere hcircle]
    rw [circleAverage_integral_eq_of_bound (fun a => (hk a).mono hV)
      (fun z hz => hm z (hV hz)) hb (fun a z hz => hbound a z (ball_subset_closedBall hz)) hs.le hB]
    exact (heq (ball_subset_closedBall hy)).symm
  have hgH := QuantumZipper.K3.harmonicOnNhd_of_meanValue g.continuous isOpen_ball hmean
  have hev : (g : ℂ → ℝ) =ᶠ[𝓝 c] (fun z => ∫ a, k a z ∂μ) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact heq (ball_subset_closedBall hz)
  exact (harmonicAt_congr_nhds hev).1 (hgH c (mem_ball_self hr))

end InteractingSLE.Restart.FlowLocalityGen
