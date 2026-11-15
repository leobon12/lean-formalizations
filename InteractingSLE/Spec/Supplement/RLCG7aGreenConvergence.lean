/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenBounds
import QuantumZipper.Proofs.GFF.K3.GreenLower3
import Mathlib.Topology.Algebra.Indicator

/-!
# Moving domination and continuous logarithmic potentials

Packet PROVE-G7A-MEANIDENT, continuation. A finite-sum adapter to dominated
convergence handles moving nonnegative dominators whose integrals converge.
Continuous compact densities have continuous logarithmic potentials by the
pinned convolution API.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric

namespace InteractingSLE.Restart.FlowLocalityGen

/-- Dominated convergence with a varying nonnegative dominator whose integral
converges to the integral of its pointwise limit. -/
theorem tendsto_integral_of_moving_bound {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    {f g : ι → α → ℝ} {b : α → ℝ}
    (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : ∀ᶠ i in l, Integrable (g i) μ)
    (hb : Integrable b μ) (hg0 : ∀ᶠ i in l, ∀ᵐ a ∂μ, 0 ≤ g i a)
    (hb0 : ∀ᵐ a ∂μ, 0 ≤ b a)
    (hfg : ∀ᶠ i in l, ∀ᵐ a ∂μ, |f i a| ≤ g i a)
    (hflim : ∀ᵐ a ∂μ, Tendsto (fun i => f i a) l (𝓝 0))
    (hglim : ∀ᵐ a ∂μ, Tendsto (fun i => g i a) l (𝓝 (b a)))
    (hmass : Tendsto (fun i => ∫ a, g i a ∂μ) l (𝓝 (∫ a, b a ∂μ))) :
    Tendsto (fun i => ∫ a, f i a ∂μ) l (𝓝 0) := by
  have htmin : Tendsto (fun i => ∫ a, min (g i a) (b a) ∂μ) l (𝓝 (∫ a, b a ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence b
    · filter_upwards [hg] with i hi using (hi.inf hb).aestronglyMeasurable
    · filter_upwards [hg0] with i hi
      filter_upwards [hi, hb0] with a ha hba
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min ha hba)]
      exact min_le_right _ _
    · exact hb
    · filter_upwards [hglim] with a ha
      simpa only [min_self] using ha.min (tendsto_const_nhds (x := b a))
  have hdiff : Tendsto (fun i => ∫ a, |g i a - b a| ∂μ) l (𝓝 0) := by
    have ht := (hmass.add (tendsto_const_nhds (x := ∫ a, b a ∂μ))).sub (htmin.const_mul 2)
    have he : (fun i => (∫ a, g i a ∂μ) + (∫ a, b a ∂μ) -
        2 * ∫ a, min (g i a) (b a) ∂μ) =ᶠ[l] fun i => ∫ a, |g i a - b a| ∂μ := by
      filter_upwards [hg] with i hi
      have iA : Integrable (fun a => g i a + b a) μ := hi.add hb
      have iM : Integrable (fun a => 2 * min (g i a) (b a)) μ := (hi.inf hb).const_mul 2
      rw [← integral_add hi hb, ← integral_const_mul, ← integral_sub iA iM]
      refine integral_congr_ae (ae_of_all _ fun a => ?_)
      dsimp only
      rcases le_total (g i a) (b a) with ha | ha
      · rw [min_eq_left ha, abs_of_nonpos (sub_nonpos.2 ha)]
        ring
      · rw [min_eq_right ha, abs_of_nonneg (sub_nonneg.2 ha)]
        ring
    have hval : (∫ a, b a ∂μ) + (∫ a, b a ∂μ) - 2 * (∫ a, b a ∂μ) = 0 := by ring
    rw [hval] at ht
    exact ht.congr' he
  have hfmin : Tendsto (fun i => ∫ a, min |f i a| (b a) ∂μ) l (𝓝 0) := by
    have ht : Tendsto (fun i => ∫ a, min |f i a| (b a) ∂μ) l
        (𝓝 (∫ a, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_filter_of_dominated_convergence b
      · filter_upwards [hf] with i hi using (hi.abs.inf hb).aestronglyMeasurable
      · exact Eventually.of_forall fun i => hb0.mono fun a ha => by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) ha)]
          exact min_le_right _ _
      · exact hb
      · filter_upwards [hflim, hb0] with a ha hba
        simpa only [abs_zero, min_eq_left hba] using ha.abs.min (tendsto_const_nhds (x := b a))
    simpa only [integral_zero] using ht
  have hupper : Tendsto (fun i => (∫ a, min |f i a| (b a) ∂μ) +
      ∫ a, |g i a - b a| ∂μ) l (𝓝 0) := by
    simpa only [add_zero] using hfmin.add hdiff
  refine squeeze_zero_norm' ?_ hupper
  filter_upwards [hf, hg, hfg] with i hi hgi hbi
  refine (norm_integral_le_integral_norm _).trans ?_
  have iM : Integrable (fun a => min |f i a| (b a)) μ := hi.abs.inf hb
  have iD : Integrable (fun a => |g i a - b a|) μ := (hgi.sub hb).abs
  rw [← integral_add iM iD]
  refine integral_mono_ae hi.norm ((hi.abs.inf hb).add (hgi.sub hb).abs) (hbi.mono fun a ha => ?_)
  dsimp only
  rw [Real.norm_eq_abs]
  rcases le_total |f i a| (b a) with hab | hba
  · rw [min_eq_left hab]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · rw [min_eq_right hba]
    linarith only [ha, le_abs_self (g i a - b a)]

/-- Logarithmic potentials of continuous compact densities are continuous.
This is the continuous version of the host's smooth-potential construction. -/
theorem continuous_Vpot {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Continuous (QuantumZipper.K3.Vpot φ) := by
  have hc := hφc.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hφ
    QuantumZipper.K3.locallyIntegrable_log_norm
  have he := funext (QuantumZipper.K3.Vpot_eq_conv φ)
  rw [← he] at hc
  exact hc

end InteractingSLE.Restart.FlowLocalityGen
