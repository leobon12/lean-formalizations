/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenKernel

/-!
# The active potential vanishes at every continuous inverse-chart boundary access

Packet PROVE-G7A-MEANIDENT. Green monotonicity and the continuous physical
Green envelope give moving domination. Thus no separation of the source from
the filled hull or from its boundary is needed for the boundary limit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv greenH)
open scoped ComplexConjugate

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- The active Green potential tends to zero at every real inverse-chart access. -/
theorem tendsto_aliveGreenPot_boundary (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {Ψ : ℂ → ℂ}
    (hΨeq : EqOn Ψ (fwdMapInv w t) H) (hΨc : ContinuousOn Ψ Hbar) (x : ℝ) :
    Tendsto (fun ξ => aliveGreenPot F w t (Ψ ξ)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  classical
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hxne : (𝓝[H] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact hxH
  have hΨlim : Tendsto Ψ (𝓝[H] (x : ℂ)) (𝓝 (Ψ x)) :=
    ((hΨc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto
  have hΨD : ∀ ξ ∈ H, Ψ ξ ∈ H \ fwdHull w t := fun ξ hξ => by
    rw [hΨeq hξ]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hξ
  have hΨH : Ψ x ∈ Hbar := by
    apply (isClosed_le continuous_const Complex.continuous_im).mem_of_tendsto hΨlim
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    exact le_of_lt (show 0 < (Ψ ξ).im from (hΨD ξ hξ).1)
  let g : ℂ → ℂ → ℝ := fun ξ a =>
    |greenH (Ψ ξ) a * H.indicator (QuantumZipper.K3.greenDensity F.f) a|
  let b : ℂ → ℝ := fun a => |greenH (Ψ x) a * H.indicator (QuantumZipper.K3.greenDensity F.f) a|
  have hf : ∀ᶠ ξ in 𝓝[H] (x : ℂ), Integrable (chartGreenIntegrand F w t ξ) := by
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    exact integrable_chartGreenIntegrand F hw hw0 ht hξ
  have hg : ∀ᶠ ξ in 𝓝[H] (x : ℂ), Integrable (g ξ) :=
    Eventually.of_forall fun ξ => integrable_greenEnvelope F (Ψ ξ)
  have hfg : ∀ᶠ ξ in 𝓝[H] (x : ℂ), ∀ᵐ a ∂(volume : Measure ℂ),
      |chartGreenIntegrand F w t ξ a| ≤ g ξ a := by
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    have hb := chartGreenIntegrand_le_envelope F hw ht (hΨD ξ hξ)
    have he : fwdMap w t (Ψ ξ) = ξ := by
      rw [hΨeq hξ, QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 ht hξ]
    rw [he] at hb
    exact hb
  have hflim : ∀ᵐ a ∂(volume : Measure ℂ), Tendsto (fun ξ => chartGreenIntegrand F w t ξ a)
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
    refine ae_of_all _ fun a => ?_
    by_cases ha : a ∈ H \ fwdHull w t
    · have hfa := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht ha
      have hh : Tendsto (fun ξ => greenH ξ (fwdMap w t a) *
          (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f) a)
          (𝓝[H] (x : ℂ)) (𝓝 (0 *
            (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f) a)) :=
        ((tendsto_greenH_real hfa x).mono_left nhdsWithin_le_nhds).mul_const _
      simpa only [zero_mul, chartGreenIntegrand] using hh
    · simp only [chartGreenIntegrand, indicator_of_notMem ha, mul_zero]
      exact tendsto_const_nhds
  have hglim : ∀ᵐ a ∂(volume : Measure ℂ), Tendsto (fun ξ => g ξ a)
      (𝓝[H] (x : ℂ)) (𝓝 (b a)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton (Ψ x))] with a hax
    by_cases ha : a ∈ H
    · have hxc : Ψ x ≠ conj a := by
        intro he
        have hi : 0 ≤ (Ψ x).im := hΨH
        rw [he, Complex.conj_im] at hi
        have ha' : 0 < a.im := ha
        linarith
      exact (((continuousAt_greenH_left (Ne.symm hax) hxc).tendsto.comp hΨlim).mul_const
        (H.indicator (QuantumZipper.K3.greenDensity F.f) a)).abs
    · simp only [g, b, indicator_of_notMem ha, mul_zero, abs_zero]
      exact tendsto_const_nhds
  have hmass : Tendsto (fun ξ => ∫ a, g ξ a) (𝓝[H] (x : ℂ)) (𝓝 (∫ a, b a)) :=
    tendsto_integral_greenEnvelope F hΨlim
      (by filter_upwards [self_mem_nhdsWithin] with ξ hξ
          exact le_of_lt (show 0 < (Ψ ξ).im from (hΨD ξ hξ).1)) hΨH
  have hlim := tendsto_integral_of_moving_bound hf hg (integrable_greenEnvelope F (Ψ x))
    (Eventually.of_forall fun _ => ae_of_all _ fun _ => abs_nonneg _)
    (ae_of_all _ fun _ => abs_nonneg _) hfg hflim hglim hmass
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  simp only [aliveGreenPot, GB7a.greenPot, chartGreenIntegrand]
  rw [hΨeq hξ, QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 ht hξ]

/-- The boundary-value clause of `AliveGreenRegularityStatement` is unconditional. -/
theorem tendsto_greenCorrection_boundary (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {Ψ : ℂ → ℂ}
    (hΨeq : EqOn Ψ (fwdMapInv w t) H) (hΨc : ContinuousOn Ψ Hbar) (x : ℝ) :
    Tendsto (greenCorrection F w t Ψ) (𝓝[H] (x : ℂ)) (𝓝 (F.f (Ψ x))) := by
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hΨlim := ((hΨc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto
  have ht' := ((F.smooth.continuous.tendsto (Ψ x)).comp hΨlim).sub
    (tendsto_aliveGreenPot_boundary F hw hw0 ht hΨeq hΨc x)
  simp only [Function.comp_apply, sub_zero] at ht'
  exact ht'

end InteractingSLE.Restart.FlowLocalityGen
