import HigherDimLFPP.Field.LogEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic energy with unbounded support

The negative part of the logarithm is controlled by a small-ball estimate; a
logarithmic moment controls the positive part.  This is the extension of the
bounded-support criterion needed for convolution densities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem log_norm_sub_le_logMoments (x y : Rd d) :
    Real.log ‖x - y‖ ≤ Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
  have hx : 0 < 2 + ‖x‖ := by positivity
  have hy : 0 < 2 + ‖y‖ := by positivity
  have hxy : ‖x - y‖ ≤ (2 + ‖x‖) * (2 + ‖y‖) := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ (2 + ‖x‖) * (2 + ‖y‖) := by nlinarith [norm_nonneg x, norm_nonneg y]
  rw [← Real.log_mul hx.ne' hy.ne']
  by_cases hzero : x = y
  · subst y
    simp only [sub_self, norm_zero, Real.log_zero]
    have hx1 : 1 ≤ 2 + ‖x‖ := by nlinarith [norm_nonneg x]
    exact Real.log_nonneg (by nlinarith [hx1, norm_nonneg x])
  · exact Real.log_le_log (norm_sub_pos_iff.mpr hzero) hxy

private theorem abs_log_norm_sub_le (x y : Rd d) :
    |Real.log ‖x - y‖| ≤
      max 0 (-Real.log ‖x - y‖) +
        (Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖)) := by
  have hpos : 0 ≤ Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) :=
    add_nonneg (Real.log_nonneg (by nlinarith [norm_nonneg x]))
      (Real.log_nonneg (by nlinarith [norm_nonneg y]))
  by_cases h : Real.log ‖x - y‖ ≤ 0
  · rw [abs_of_nonpos h]
    exact le_add_of_le_of_nonneg (le_max_right _ _) hpos
  · rw [abs_of_pos (lt_of_not_ge h)]
    exact le_add_of_nonneg_of_le (le_max_left _ _) (log_norm_sub_le_logMoments x y)

/-- A finite measure with a linear small-ball bound and finite logarithmic
moment has finite absolute logarithmic self-energy. -/
theorem integrable_log_norm_sub_of_smallBall_logMoment
    {lam : Measure (Rd d)} [IsFiniteMeasure lam] {A : ℝ} (hA : 0 ≤ A)
    (hball : ∀ z : Rd d, ∀ s > 0, lam.real (closedBall z s) ≤ A * s)
    (hmoment : Integrable (fun z : Rd d => Real.log (2 + ‖z‖)) lam) :
    Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) (lam.prod lam) := by
  let negPart : Rd d × Rd d → ℝ := fun p => max 0 (-Real.log ‖p.1 - p.2‖)
  have hnegMeas : Measurable negPart :=
    measurable_const.max ((measurable_fst.sub measurable_snd).norm.log.neg)
  have hnegFin : ∫⁻ p, ENNReal.ofReal (negPart p) ∂(lam.prod lam) < ⊤ := by
    rw [lintegral_prod _ hnegMeas.ennreal_ofReal.aemeasurable]
    calc
      ∫⁻ z, ∫⁻ w, ENNReal.ofReal (negPart (z, w)) ∂lam ∂lam
          ≤ ∫⁻ _z, ENNReal.ofReal A ∂lam :=
            lintegral_mono fun z => HigherDimLFPP.FieldAux.lintegral_log_inv_le hA hball z
      _ = ENNReal.ofReal A * lam univ := lintegral_const _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hneg : Integrable negPart (lam.prod lam) :=
    (lintegral_ofReal_ne_top_iff_integrable hnegMeas.aestronglyMeasurable
      (ae_of_all _ fun _ => le_max_left _ _)).mp hnegFin.ne
  have hupper : Integrable
      (fun p : Rd d × Rd d => Real.log (2 + ‖p.1‖) + Real.log (2 + ‖p.2‖))
      (lam.prod lam) :=
    (hmoment.comp_fst lam).add (hmoment.comp_snd lam)
  have hlogMeas : Measurable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) :=
    (measurable_fst.sub measurable_snd).norm.log
  exact Integrable.mono' (hneg.add hupper) hlogMeas.aestronglyMeasurable
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact abs_log_norm_sub_le p.1 p.2)

/-- Criterion for log pairability using a logarithmic moment in place of a
bounded-support hypothesis.  A bounded density implies the required small-ball
bound in dimension at least one. -/
theorem logPairable_of_logMoment
    {μ ν μ' ν' : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    [NullSingletonClass μ] [NullSingletonClass ν]
    [NullSingletonClass μ'] [NullSingletonClass ν']
    {A : ℝ} (hA : 0 ≤ A)
    (hball : ∀ z : Rd d, ∀ s > 0,
      (μ + ν + μ' + ν').real (closedBall z s) ≤ A * s)
    (hmoment : Integrable (fun z : Rd d => Real.log (2 + ‖z‖))
      (μ + ν + μ' + ν')) :
    HigherDimLFPP.LogPairable μ ν μ' ν' := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    integrable_log_norm_sub_of_smallBall_logMoment hA hball hmoment⟩

end HigherDimLQGMetric
