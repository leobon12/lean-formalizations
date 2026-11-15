/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenResidual

/-!
# Integrating the regular residual kernel

Packet PROVE-G7A-MEANIDENT. The regular kernel has the same integrals as the
raw Green difference, since its exceptional diagonal is null. The positive
and negative parts of the cutoff density give integrable nonnegative kernels.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap greenH)

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- The weighted regular kernel agrees almost everywhere with a measurable
raw Green difference. -/
theorem residualGreenKernel_mul_eq {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ}
    (ht : 0 ≤ t) {z a : ℂ} (hz : z ∈ H \ fwdHull w t) (hza : z ≠ a) (c : ℂ → ℝ) :
    c a * residualGreenKernel w t a z =
      greenH z a * H.indicator c a -
        greenH (fwdMap w t z) (LocalExt.fwdAlive w t a) * (H \ fwdHull w t).indicator c a := by
  classical
  by_cases ha : a ∈ H
  · rw [residualGreenKernel_eq hw ht hz ha hza, indicator_of_mem ha]
    by_cases haD : a ∈ H \ fwdHull w t
    · rw [indicator_of_mem haD, indicator_of_mem haD, LocalExt.fwdAlive,
        piecewise_eq_of_mem _ _ _ haD]
      ring
    · rw [indicator_of_notMem haD, indicator_of_notMem haD, mul_zero, sub_zero, sub_zero, mul_comm]
  · have haD : a ∉ H \ fwdHull w t := fun he => ha he.1
    rw [residualGreenKernel, ite_eq_right ha, indicator_of_notMem ha,
      indicator_of_notMem haD, mul_zero, mul_zero, mul_zero, sub_zero]

/-- Each weighted residual section is measurable up to its removable diagonal. -/
theorem aestronglyMeasurable_residualGreenKernel_mul {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull w t)
    {c : ℂ → ℝ} (hc : Measurable c) :
    AEStronglyMeasurable (fun a => c a * residualGreenKernel w t a z) volume := by
  have hm : Measurable (fun a => greenH z a * H.indicator c a -
      greenH (fwdMap w t z) (LocalExt.fwdAlive w t a) * (H \ fwdHull w t).indicator c a) :=
    ((QuantumZipper.measurable_greenH.comp (measurable_const.prodMk measurable_id)).mul
      (hc.indicator QuantumZipper.isOpen_H.measurableSet)).sub
      ((QuantumZipper.measurable_greenH.comp
        (measurable_const.prodMk (LocalExt.measurable_fwdAlive hw ht))).mul
          (hc.indicator (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht).measurableSet))
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)] with a haz
  exact (residualGreenKernel_mul_eq hw ht hz (Ne.symm haz) c).symm

/-- A density bounded by the absolute cutoff density gives an integrable residual kernel. -/
theorem integrable_residualGreenKernel_mul (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull w t)
    {c : ℂ → ℝ} (hc : Measurable c) (hcF : ∀ a, |c a| ≤ |QuantumZipper.K3.greenDensity F.f a|) :
    Integrable (fun a => c a * residualGreenKernel w t a z) := by
  classical
  refine (integrable_greenEnvelope F z).mono'
    (aestronglyMeasurable_residualGreenKernel_mul hw ht hz hc) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)] with a haz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (residualGreenKernel_nonneg hw ht a hz)]
  by_cases ha : a ∈ H
  · have hg := QuantumZipper.greenH_nonneg
      (show z ∈ Hbar from le_of_lt (show 0 < z.im from hz.1))
      (show a ∈ Hbar from le_of_lt (show 0 < a.im from ha)) (Ne.symm haz)
    have hkle : residualGreenKernel w t a z ≤ greenH z a := by
      rw [residualGreenKernel_eq hw ht hz ha (Ne.symm haz)]
      refine sub_le_self _ ?_
      by_cases haD : a ∈ H \ fwdHull w t
      · rw [indicator_of_mem haD]
        exact (GB7a.greenH_fwdMap_le hw ht hz haD (Ne.symm haz)).1
      · rw [indicator_of_notMem haD]
    rw [indicator_of_mem ha, abs_mul, abs_of_nonneg hg, mul_comm (greenH z a)]
    exact mul_le_mul (hcF a) hkle (residualGreenKernel_nonneg hw ht a hz) (abs_nonneg _)
  · simp only [residualGreenKernel, ite_eq_right ha, mul_zero,
      indicator_of_notMem ha, abs_zero, le_refl]

/-- The integrated residual kernel is exactly the physical Green correction. -/
theorem integral_residualGreenKernel_density (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull w t) :
    (∫ a, QuantumZipper.K3.greenDensity F.f a * residualGreenKernel w t a z) =
      F.f z - aliveGreenPot F w t z := by
  classical
  obtain ⟨_, _, _, hs⟩ := exists_density_source_bounds F
  have i1 := hs.integrable_greenH_mul z
  have hξ := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hz
  have i2 : Integrable (fun a => greenH (fwdMap w t z) (LocalExt.fwdAlive w t a) *
      (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f) a) := by
    refine (integrable_chartGreenIntegrand F hw hw0 ht hξ).congr (ae_of_all _ fun a => ?_)
    by_cases ha : a ∈ H \ fwdHull w t
    · simp only [chartGreenIntegrand, LocalExt.fwdAlive, piecewise_eq_of_mem _ _ _ ha]
    · simp only [chartGreenIntegrand, indicator_of_notMem ha, mul_zero]
  have he : (∫ a, QuantumZipper.K3.greenDensity F.f a * residualGreenKernel w t a z) =
      (∫ a, greenH z a * H.indicator (QuantumZipper.K3.greenDensity F.f) a) -
        ∫ a, greenH (fwdMap w t z) (LocalExt.fwdAlive w t a) *
          (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f) a := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)] with a haz
    exact residualGreenKernel_mul_eq hw ht hz (Ne.symm haz) _
  rw [he, GB7a.integral_greenH_mul_indicator_greenDensity
    (F.smooth.of_le (by simp)) F.compact F.odd]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  by_cases ha : a ∈ H \ fwdHull w t
  · simp only [LocalExt.fwdAlive, piecewise_eq_of_mem _ _ _ ha]
  · simp only [indicator_of_notMem ha, mul_zero]

end InteractingSLE.Restart.FlowLocalityGen
