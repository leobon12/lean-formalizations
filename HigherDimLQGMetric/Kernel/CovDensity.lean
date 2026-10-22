import HigherDimLQGMetric.Kernel.FourierConvMeasure
import HigherDimLQGMetric.Kernel.CovLogMoment

/-!
# Finite density measures with logarithmic moments
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {f : Rd d → ℝ}

theorem isFiniteMeasure_posM_of_integrable (hf : Integrable f) :
    IsFiniteMeasure (posM f) := by
  unfold posM
  exact isFiniteMeasure_withDensity_ofReal hf.2

theorem posM_apply_le_of_bound {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (s : Set (Rd d)) :
    posM f s ≤ ENNReal.ofReal M * volume s := by
  rw [posM, withDensity_apply']
  calc
    ∫⁻ z in s, ENNReal.ofReal (f z) ≤ ∫⁻ _z in s, ENNReal.ofReal M :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM z))
    _ = ENNReal.ofReal M * volume s := by rw [setLIntegral_const]

theorem posM_real_closedBall_le_of_bound [NeZero d]
    (hf : Integrable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (z : Rd d) {s : ℝ} (hs : 0 < s) :
    (posM f).real (closedBall z s) ≤
      (M * volBall d + (posM f).real univ) * s := by
  haveI : IsFiniteMeasure (posM f) := isFiniteMeasure_posM_of_integrable hf
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hV := volBall_nonneg (d := d)
  have hmass : 0 ≤ (posM f).real univ := measureReal_nonneg
  rcases le_or_gt s 1 with hs1 | hs1
  · have h1 : (posM f).real (closedBall z s) ≤ M * (s ^ d * volBall d) := by
      rw [← volume_closedBall_real z hs.le, Measure.real]
      have h2 := posM_apply_le_of_bound hM (closedBall z s)
      have h3 : ENNReal.ofReal M * volume (closedBall z s) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
      calc
        ((posM f) (closedBall z s)).toReal ≤
            (ENNReal.ofReal M * volume (closedBall z s)).toReal :=
          ENNReal.toReal_mono h3 h2
        _ = M * (volume (closedBall z s)).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0]
    have h4 : s ^ d ≤ s := pow_le_of_le_one hs.le hs1 (NeZero.ne d)
    calc
      (posM f).real (closedBall z s) ≤ M * (s ^ d * volBall d) := h1
      _ ≤ M * (s * volBall d) := by gcongr
      _ ≤ (M * volBall d + (posM f).real univ) * s := by nlinarith
  · calc
      (posM f).real (closedBall z s) ≤ (posM f).real univ :=
        measureReal_mono (subset_univ _)
      _ ≤ (posM f).real univ * s := le_mul_of_one_le_right hmass hs1.le
      _ ≤ (M * volBall d + (posM f).real univ) * s :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (mul_nonneg hM0 hV)) hs.le

theorem integrable_logWeight_posM (hmeas : Measurable f)
    (hfw : Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * f x)) :
    Integrable (fun x : Rd d => Real.log (2 + ‖x‖)) (posM f) := by
  rw [posM, integrable_withDensity_iff_integrable_smul' hmeas.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hfw' := hfw.norm
  apply hfw'.mono'
  · have hm : Measurable (fun x : Rd d =>
        (ENNReal.ofReal (f x)).toReal • Real.log (2 + ‖x‖)) := by
      fun_prop
    exact hm.aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      have hw : 0 ≤ Real.log (2 + ‖x‖) :=
        Real.log_nonneg (by nlinarith [norm_nonneg x])
      simp only [ENNReal.toReal_ofReal', smul_eq_mul, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg hw]
      rw [abs_of_nonneg (le_max_right (f x) 0)]
      simpa only [mul_comm (Real.log (2 + ‖x‖))] using
        (mul_le_mul_of_nonneg_right
          (max_le (le_abs_self (f x)) (abs_nonneg (f x))) hw)

theorem integral_eq_posM_sub_posM_of_integrable
    (hf : Integrable f) :
    ∫ x, f x = (posM f).real univ - (posM (-f)).real univ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, Measure.real,
    Measure.real, posM_univ, posM_univ]
  rfl

theorem logPairable_posM_of_logMoment [NeZero d]
    {f g : Rd d → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hmf : Measurable f) (hmg : Measurable g)
    {M M' : ℝ} (hMf : ∀ x, |f x| ≤ M) (hMg : ∀ x, |g x| ≤ M')
    (hwf : Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * f x))
    (hwg : Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * g x)) :
    HigherDimLFPP.LogPairable (posM f) (posM (-f)) (posM g) (posM (-g)) := by
  haveI : IsFiniteMeasure (posM f) := isFiniteMeasure_posM_of_integrable hf
  haveI : IsFiniteMeasure (posM (-f)) := isFiniteMeasure_posM_of_integrable hf.neg
  haveI : IsFiniteMeasure (posM g) := isFiniteMeasure_posM_of_integrable hg
  haveI : IsFiniteMeasure (posM (-g)) := isFiniteMeasure_posM_of_integrable hg.neg
  haveI : NullSingletonClass (posM f) := nullSingletonClass_posM f
  haveI : NullSingletonClass (posM (-f)) := nullSingletonClass_posM (-f)
  haveI : NullSingletonClass (posM g) := nullSingletonClass_posM g
  haveI : NullSingletonClass (posM (-g)) := nullSingletonClass_posM (-g)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMf 0)
  have hM0' : 0 ≤ M' := (abs_nonneg _).trans (hMg 0)
  let A₁ := M * volBall d + (posM f).real univ
  let A₂ := M * volBall d + (posM (-f)).real univ
  let A₃ := M' * volBall d + (posM g).real univ
  let A₄ := M' * volBall d + (posM (-g)).real univ
  have ha₁ : 0 ≤ A₁ := add_nonneg (mul_nonneg hM0 volBall_nonneg) measureReal_nonneg
  have ha₂ : 0 ≤ A₂ := add_nonneg (mul_nonneg hM0 volBall_nonneg) measureReal_nonneg
  have ha₃ : 0 ≤ A₃ := add_nonneg (mul_nonneg hM0' volBall_nonneg) measureReal_nonneg
  have ha₄ : 0 ≤ A₄ := add_nonneg (mul_nonneg hM0' volBall_nonneg) measureReal_nonneg
  have h₁ : ∀ z : Rd d, ∀ s > 0, (posM f).real (closedBall z s) ≤ A₁ * s :=
    fun z s hs => posM_real_closedBall_le_of_bound hf hMf z hs
  have h₂ : ∀ z : Rd d, ∀ s > 0, (posM (-f)).real (closedBall z s) ≤ A₂ * s :=
    fun z s hs => posM_real_closedBall_le_of_bound hf.neg
      (fun x => by simpa only [Pi.neg_apply, abs_neg] using hMf x) z hs
  have h₃ : ∀ z : Rd d, ∀ s > 0, (posM g).real (closedBall z s) ≤ A₃ * s :=
    fun z s hs => posM_real_closedBall_le_of_bound hg hMg z hs
  have h₄ : ∀ z : Rd d, ∀ s > 0, (posM (-g)).real (closedBall z s) ≤ A₄ * s :=
    fun z s hs => posM_real_closedBall_le_of_bound hg.neg
      (fun x => by simpa only [Pi.neg_apply, abs_neg] using hMg x) z hs
  have hball := real_closedBall_add_le
    (real_closedBall_add_le (real_closedBall_add_le h₁ h₂) h₃) h₄
  have hwfneg : Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * (-f x)) := by
    convert hwf.neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hwgneg : Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * (-g x)) := by
    convert hwg.neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hmoment := (((integrable_logWeight_posM hmf hwf).add_measure
    (integrable_logWeight_posM hmf.neg hwfneg)).add_measure
      (integrable_logWeight_posM hmg hwg)).add_measure
        (integrable_logWeight_posM hmg.neg hwgneg)
  exact logPairable_of_logMoment
    (add_nonneg (add_nonneg (add_nonneg ha₁ ha₂) ha₃) ha₄) hball hmoment

end HigherDimLQGMetric
