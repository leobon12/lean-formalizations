/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenEnvelope

/-!
# The active Green integrand in the half-plane chart

Packet PROVE-G7A-MEANIDENT. Reuse the measurable alive forward map and the
landed Green monotonicity estimate. In particular the restricted integral is
an actual integrable kernel, rather than a nonintegrable Bochner default.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap greenH)
open scoped ComplexConjugate

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- The active-domain density paired with the Green kernel in the final chart. -/
def chartGreenIntegrand (F : CMCut) (w : ℝ → ℝ) (t : ℝ) (ξ a : ℂ) : ℝ :=
  greenH ξ (fwdMap w t a) *
    (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f) a

/-- The active indicator allows use of the landed measurable alive-map version. -/
theorem measurable_chartGreenIntegrand (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℂ) : Measurable (chartGreenIntegrand F w t ξ) := by
  classical
  have hm : Measurable (fun a => greenH ξ (LocalExt.fwdAlive w t a) *
      (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f) a) :=
    (QuantumZipper.measurable_greenH.comp
    (measurable_const.prodMk (LocalExt.measurable_fwdAlive hw ht))).mul
      (F.continuous_greenDensity.measurable.indicator
        (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht).measurableSet)
  convert hm using 1
  funext a
  by_cases ha : a ∈ H \ fwdHull w t
  · simp only [chartGreenIntegrand, LocalExt.fwdAlive, piecewise_eq_of_mem _ _ _ ha]
  · simp only [chartGreenIntegrand, indicator_of_notMem ha, mul_zero]

/-- Green monotonicity dominates the chart kernel by a physical half-plane kernel. -/
theorem chartGreenIntegrand_le_envelope (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull w t) :
    ∀ᵐ a ∂(volume : Measure ℂ), |chartGreenIntegrand F w t (fwdMap w t z) a| ≤
      |greenH z a * H.indicator (QuantumZipper.K3.greenDensity F.f) a| := by
  classical
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)] with a haz
  by_cases ha : a ∈ H \ fwdHull w t
  · have hg := GB7a.greenH_fwdMap_le hw ht hz ha (Ne.symm haz)
    have hg0 := QuantumZipper.greenH_nonneg
      (show z ∈ Hbar from le_of_lt (show 0 < z.im from hz.1))
      (show a ∈ Hbar from le_of_lt (show 0 < a.im from ha.1)) (Ne.symm haz)
    rw [chartGreenIntegrand, indicator_of_mem ha, indicator_of_mem ha.1,
      abs_mul, abs_mul, abs_of_nonneg hg.1, abs_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_right hg.2 (abs_nonneg _)
  · rw [chartGreenIntegrand, indicator_of_notMem ha, mul_zero, abs_zero]
    exact abs_nonneg _

/-- Every chart point in H gives an integrable active kernel. -/
theorem integrable_chartGreenIntegrand (F : CMCut) {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {ξ : ℂ} (hξ : ξ ∈ H) :
    Integrable (chartGreenIntegrand F w t ξ) := by
  set z := QuantumZipper.fwdMapInv w t ξ
  have hz := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hξ
  have hξeq := QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 ht hξ
  have hbd := chartGreenIntegrand_le_envelope F hw ht hz
  rw [hξeq] at hbd
  exact (integrable_greenEnvelope F z).mono'
    (measurable_chartGreenIntegrand F hw ht ξ).aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hbd)

/-- The half-plane Green kernel tends to zero at a real boundary point. -/
theorem tendsto_greenH_real {a : ℂ} (ha : a ∈ H) (x : ℝ) :
    Tendsto (fun ξ => greenH ξ a) (𝓝 (x : ℂ)) (𝓝 0) := by
  have hxa : (x : ℂ) ≠ a := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.ofReal_im] at hi
    have ha' : 0 < a.im := ha
    linarith
  have hxc : (x : ℂ) ≠ conj a := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.ofReal_im, Complex.conj_im] at hi
    have ha' : 0 < a.im := ha
    linarith
  have ht := (continuousAt_greenH_left hxa hxc).tendsto
  have he : greenH (x : ℂ) a = 0 := by
    rw [greenH, QuantumZipper.norm_sub_conj_comm, Complex.conj_ofReal, norm_sub_rev, sub_self]
  rw [he] at ht
  exact ht

end InteractingSLE.Restart.FlowLocalityGen
