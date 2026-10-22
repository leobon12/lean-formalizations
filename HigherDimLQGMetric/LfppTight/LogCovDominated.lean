import HigherDimLQGMetric.LfppTight.TotalEnvelope
import HigherDimLQGMetric.Frozen.LogCovRd

/-! Bounding a test-function covariance by the log energy of a dominating positive measure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_abs_logCovRd_le_energy {d : ℕ}
    (f : Rd d → ℝ) (hf : Integrable f) (hfm : Measurable f)
    (lam : Measure (Rd d)) [IsFiniteMeasure lam]
    (hdom : posM (fun x => |f x|) ≤ lam)
    (hlog : Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖)
      (lam.prod lam)) :
    |logCovRd f f| ≤
      ∫ p : Rd d × Rd d, |Real.log ‖p.1 - p.2‖| ∂(lam.prod lam) := by
  let μf : Measure (Rd d) := posM (fun x => |f x|)
  letI : IsFiniteMeasure μf := isFiniteMeasure_posM_of_integrable hf.abs
  have hprod : μf.prod μf ≤ lam.prod lam := Measure.prod_mono hdom hdom
  have hlogμ : Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖)
      (μf.prod μf) := hlog.mono_measure hprod
  have hlogabs : Integrable (fun p : Rd d × Rd d =>
      |Real.log ‖p.1 - p.2‖|) (μf.prod μf) := by
    convert hlogμ.norm using 1
    funext p
    exact Real.norm_eq_abs _
  have hfa : Measurable (fun x : Rd d => |f x|) := continuous_abs.measurable.comp hfm
  have hFabs : Integrable (fun p : Rd d × Rd d =>
      |f p.1| * |f p.2| * |Real.log ‖p.1 - p.2‖|) := by
    have hi := (integrable_prod_posM_iff hfa hfa
      (fun p : Rd d × Rd d => |Real.log ‖p.1 - p.2‖|)).mp hlogabs
    convert hi using 1
    funext p
    simp only [max_eq_left (abs_nonneg (f p.1)),
      max_eq_left (abs_nonneg (f p.2))]
  have hF : Integrable (fun p : Rd d × Rd d =>
      f p.1 * (-Real.log ‖p.1 - p.2‖) * f p.2) := by
    apply hFabs.mono'
    · exact ((hfm.comp measurable_fst).aestronglyMeasurable.mul
        ((measurable_fst.sub measurable_snd).norm.log.neg).aestronglyMeasurable).mul
          (hfm.comp measurable_snd).aestronglyMeasurable
    · exact ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
        exact le_of_eq (by ring)
  have hcov : logCovRd f f = ∫ p : Rd d × Rd d,
      f p.1 * (-Real.log ‖p.1 - p.2‖) * f p.2 := by
    rw [logCovRd, Measure.volume_eq_prod (Rd d) (Rd d), integral_prod _ hF]
  have heq : (∫ p : Rd d × Rd d,
      |f p.1 * (-Real.log ‖p.1 - p.2‖) * f p.2|) =
      ∫ p : Rd d × Rd d, |Real.log ‖p.1 - p.2‖| ∂(μf.prod μf) := by
    rw [integral_prod_posM hfa hfa
      (fun p : Rd d × Rd d => |Real.log ‖p.1 - p.2‖|)]
    apply integral_congr_ae
    exact ae_of_all _ fun p => by
      simp only [abs_mul, abs_neg]
      rw [max_eq_left (abs_nonneg (f p.1)), max_eq_left (abs_nonneg (f p.2))]
      ring
  calc
    |logCovRd f f| =
        |∫ p : Rd d × Rd d, f p.1 * (-Real.log ‖p.1 - p.2‖) * f p.2| :=
      congrArg abs hcov
    _ ≤ ∫ p : Rd d × Rd d,
        |f p.1 * (-Real.log ‖p.1 - p.2‖) * f p.2| := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (f := fun p : Rd d × Rd d =>
              f p.1 * (-Real.log ‖p.1 - p.2‖) * f p.2)
    _ = ∫ p : Rd d × Rd d,
        |Real.log ‖p.1 - p.2‖| ∂(μf.prod μf) := heq
    _ ≤ ∫ p : Rd d × Rd d,
        |Real.log ‖p.1 - p.2‖| ∂(lam.prod lam) :=
      integral_mono_measure hprod (ae_of_all _ fun p => abs_nonneg _) hlog.norm

end HigherDimLQGMetric
