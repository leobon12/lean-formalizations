/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenConvergence

/-!
# A continuous envelope for moving half-plane Green kernels

Packet PROVE-G7A-MEANIDENT. Oddness of the cutoff makes the absolute density,
extended by zero below the real line, continuous. Its logarithmic potential
therefore supplies a continuous integral envelope, including at boundary points.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar greenH)
open scoped ComplexConjugate

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- The absolute cutoff density, zero outside H. -/
def envelopeDensity (F : CMCut) : ℂ → ℝ :=
  H.indicator (fun z => |QuantumZipper.K3.greenDensity F.f z|)

/-- Oddness removes the jump of the density at the original real boundary. -/
theorem continuous_envelopeDensity (F : CMCut) : Continuous (envelopeDensity F) := by
  apply F.continuous_greenDensity.abs.indicator
  intro z hz
  have him : z.im = 0 := by
    change z ∈ frontier {z : ℂ | 0 < z.im} at hz
    rw [Complex.frontier_setOfPred_lt_im] at hz
    exact hz
  rw [GB7a.greenDensity_eq_zero_of_im_eq_zero (F.smooth.of_le (by simp)) F.odd him, abs_zero]

/-- The envelope density has compact support. -/
theorem hasCompactSupport_envelopeDensity (F : CMCut) : HasCompactSupport (envelopeDensity F) := by
  refine HasCompactSupport.of_support_subset_isCompact F.hasCompactSupport_greenDensity ?_
  intro z hz
  have hzH : z ∈ H := by
    by_contra hnot
    exact hz (indicator_of_notMem hnot _)
  have hn : QuantumZipper.K3.greenDensity F.f z ≠ 0 := by
    intro hn
    exact hz (by simp only [envelopeDensity, indicator_of_mem hzH, hn, abs_zero])
  exact subset_tsupport _ hn

/-- The absolute kernel envelope is integrable at every physical point. -/
theorem integrable_greenEnvelope (F : CMCut) (z : ℂ) :
    Integrable (fun a => |greenH z a * H.indicator (QuantumZipper.K3.greenDensity F.f) a|) := by
  obtain ⟨_, _, _, hs⟩ := exists_density_source_bounds F
  exact (hs.integrable_greenH_mul z).abs

/-- Away from reflection and diagonal poles the half-plane Green kernel is continuous. -/
theorem continuousAt_greenH_left {z a : ℂ} (hza : z ≠ a) (hzc : z ≠ conj a) :
    ContinuousAt (fun x => greenH x a) z := by
  exact (((continuous_id.sub continuous_const).norm.continuousAt.log
    (norm_ne_zero_iff.2 (sub_ne_zero.2 hzc))).sub
    ((continuous_id.sub continuous_const).norm.continuousAt.log
      (norm_ne_zero_iff.2 (sub_ne_zero.2 hza))))

/-- The absolute envelope integral on Hbar is a continuous logarithmic potential. -/
theorem integral_greenEnvelope_eq (F : CMCut) {z : ℂ} (hz : z ∈ Hbar) :
    (∫ a, |greenH z a * H.indicator (QuantumZipper.K3.greenDensity F.f) a|) =
      QuantumZipper.K3.Vpot (envelopeDensity F) (conj z) -
        QuantumZipper.K3.Vpot (envelopeDensity F) z := by
  have hφ := continuous_envelopeDensity F
  have hφc := hasCompactSupport_envelopeDensity F
  have he : (∫ a, |greenH z a * H.indicator (QuantumZipper.K3.greenDensity F.f) a|) =
      ∫ a, greenH z a * envelopeDensity F a := by
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)] with a haz
    by_cases ha : a ∈ H
    · have hg := QuantumZipper.greenH_nonneg hz
        (show a ∈ Hbar from le_of_lt (show 0 < a.im from ha)) (Ne.symm haz)
      simp only [envelopeDensity, indicator_of_mem ha, abs_mul, abs_of_nonneg hg]
    · simp only [envelopeDensity, indicator_of_notMem ha, mul_zero, abs_zero]
  rw [he, QuantumZipper.K3.Vpot, QuantumZipper.K3.Vpot, ← integral_sub
    (QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hφ hφc (conj z))
    (QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hφ hφc z)]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  change greenH z a * envelopeDensity F a =
    Real.log ‖a - conj z‖ * envelopeDensity F a - Real.log ‖a - z‖ * envelopeDensity F a
  rw [greenH, QuantumZipper.norm_sub_conj_comm z a, norm_sub_rev z a]
  ring

/-- The envelope masses converge whenever their physical arguments converge in Hbar. -/
theorem tendsto_integral_greenEnvelope (F : CMCut) {ι : Type*} {l : Filter ι}
    {z : ι → ℂ} {a : ℂ} (hza : Tendsto z l (𝓝 a))
    (hzH : ∀ᶠ i in l, z i ∈ Hbar) (haH : a ∈ Hbar) :
    Tendsto (fun i => ∫ b, |greenH (z i) b * H.indicator (QuantumZipper.K3.greenDensity F.f) b|)
      l (𝓝 (∫ b, |greenH a b * H.indicator (QuantumZipper.K3.greenDensity F.f) b|)) := by
  have hc := continuous_Vpot (continuous_envelopeDensity F) (hasCompactSupport_envelopeDensity F)
  have ht := ((hc.comp Complex.continuous_conj).tendsto a).sub (hc.tendsto a)
  have ht' := ht.comp hza
  simp only [Function.comp_apply] at ht'
  rw [← integral_greenEnvelope_eq F haH] at ht'
  refine ht'.congr' ?_
  filter_upwards [hzH] with i hi using (integral_greenEnvelope_eq F hi).symm

end InteractingSLE.Restart.FlowLocalityGen
