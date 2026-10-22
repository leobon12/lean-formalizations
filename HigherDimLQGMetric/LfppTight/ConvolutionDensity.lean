import HigherDimLQGMetric.LfppTight.ConvolutionGrowth
import HigherDimLQGMetric.Kernel.CovDensity

/-! Density of the convolution of a finite measure with a bounded nonnegative Lebesgue density. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_conv_posM_eq {d : ℕ}
    (μ : Measure (Rd d)) [IsFiniteMeasure μ]
    (f : Rd d → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) {M : ℝ} (hM : ∀ x, f x ≤ M) :
    Measure.conv μ (posM f) =
      posM (fun x => ∫ u, f (x - u) ∂μ) := by
  let e : Rd d → ℝ≥0∞ := fun x => ∫⁻ u, ENNReal.ofReal (f (x - u)) ∂μ
  have he : Measurable e := by
    dsimp [e]
    have hprod : Measurable fun p : Rd d × Rd d =>
        ENNReal.ofReal (f (p.1 - p.2)) :=
      hf.ennreal_ofReal.comp (measurable_fst.sub measurable_snd)
    exact hprod.lintegral_prod_right'
  have hmeas : Measurable (fun x : Rd d => ∫ u, f (x - u) ∂μ) := by
    have hprod : Measurable fun p : Rd d × Rd d => f (p.1 - p.2) :=
      hf.comp (measurable_fst.sub measurable_snd)
    exact hprod.stronglyMeasurable.integral_prod_right'.measurable
  have hfeq (x : Rd d) : e x = ENNReal.ofReal (∫ u, f (x - u) ∂μ) := by
    have hfi : Integrable (fun u => f (x - u)) μ := by
      apply Integrable.of_bound (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable M
      filter_upwards with u
      change ‖f (x - u)‖ ≤ M
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
      exact hM _
    exact (ofReal_integral_eq_lintegral_ofReal hfi
      (ae_of_all _ fun u => hf0 (x - u))).symm
  have hconv : Measure.conv μ (posM f) = volume.withDensity e := by
    letI : IsFiniteMeasure (posM f) := isFiniteMeasure_posM_of_integrable hfi
    apply Measure.ext_of_lintegral
    intro g hg
    rw [Measure.lintegral_conv hg]
    change (∫⁻ u, ∫⁻ a, g (u + a) ∂(volume.withDensity fun a => ENNReal.ofReal (f a)) ∂μ) = _
    have hinner0 (u : Rd d) :
        (∫⁻ a, g (u + a) ∂(volume.withDensity fun a => ENNReal.ofReal (f a))) =
          ∫⁻ a, ENNReal.ofReal (f a) * g (u + a) ∂volume := by
      exact lintegral_withDensity_eq_lintegral_mul volume hf.ennreal_ofReal
        (hg.comp (measurable_const.add measurable_id))
    simp_rw [hinner0]
    rw [lintegral_withDensity_eq_lintegral_mul volume he hg]
    change (∫⁻ u, ∫⁻ a, ENNReal.ofReal (f a) * g (u + a) ∂volume ∂μ) =
      ∫⁻ x, e x * g x ∂volume
    have hinner (u : Rd d) :
        (∫⁻ a, ENNReal.ofReal (f a) * g (u + a) ∂volume) =
          ∫⁻ x, ENNReal.ofReal (f (x - u)) * g x ∂volume := by
      have ht := MeasureTheory.lintegral_add_right_eq_self
        (μ := (volume : Measure (Rd d)))
        (fun x : Rd d => ENNReal.ofReal (f (x - u)) * g x) u
      simpa only [add_sub_cancel_right, add_comm u] using ht
    simp_rw [hinner]
    rw [lintegral_lintegral_swap (by fun_prop)]
    have hinner1 (x : Rd d) :
        (∫⁻ u, ENNReal.ofReal (f (x - u)) * g x ∂μ) = e x * g x := by
      rw [lintegral_mul_const (g x) (by fun_prop)]
    simp_rw [hinner1]
  rw [hconv]
  unfold posM
  congr 1
  funext x
  exact hfeq x

end HigherDimLQGMetric
