import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RawLocal
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3




 


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem around_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x,y) = c * D (x,y))
    (w : ℂ) (a b : ℝ) :
    Objects.CorrectedEvent.around E w a b = c * Objects.CorrectedEvent.around D w a b := by
  unfold Objects.CorrectedEvent.around
  simp only [Positivity.Witnesses.isCurve_iff_of_dist_scale D E c hc0 hcTop hscale,
    Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

theorem acr_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x,y) = c * D (x,y))
    (w : ℂ) (a b : ℝ) :
    Objects.CorrectedEvent.acr E w a b = c * Objects.CorrectedEvent.acr D w a b := by
  unfold Objects.CorrectedEvent.acr
  simp only [Positivity.Witnesses.isCurve_iff_of_dist_scale D E c hc0 hcTop hscale,
    Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

theorem regGood_iff_of_dist_scale (C : Objects.CorrectedEvent.Constants)
    (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x,y) = c * D (x,y))
    (w : ℂ) (s : ℝ) :
    Objects.CorrectedEvent.regGood C E s w ↔ Objects.CorrectedEvent.regGood C D s w := by
  rw [Objects.CorrectedEvent.regGood, Objects.CorrectedEvent.regGood,
    around_eq_mul_of_dist_scale D E c hc0 hcTop hscale,
    acr_eq_mul_of_dist_scale D E c hc0 hcTop hscale]
  have hpos (x : ℝ≥0∞) : (0 < c*x) ↔ (0 < x) := by
    rw [ENNReal.mul_pos_iff]
    simp [pos_iff_ne_zero, hc0]
  have hfin (x : ℝ≥0∞) : (c*x < ⊤) ↔ (x < ⊤) := by
    constructor
    · intro hx
      exact ENNReal.lt_top_of_mul_ne_top_right hx.ne hc0
    · intro hx
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hcTop) hx
  rw [hpos, hfin, hpos, hfin]
  rw [mul_left_comm (ENNReal.ofReal C.c_reg⁻¹) c,
    ENNReal.mul_le_mul_iff_right hc0 hcTop]

theorem ae_regGood_addConst_iff
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (w : ℂ) (s : ℝ) (c : LQGMetric.DistC → ℝ) :
    ∀ᵐ g ∂μ,
      Objects.CorrectedEvent.regGood C (D (LQGMetric.addConst g (c g))) s w ↔
        Objects.CorrectedEvent.regGood C (D g) s w := by
  have hwhole : LQGMetric.IsGFFPlusCont
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD c] with g hg
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c g))
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heTop : e ≠ ∞ := ENNReal.ofReal_ne_top
  exact regGood_iff_of_dist_scale C (D g)
    (D (LQGMetric.addConst g (c g))) e he0 heTop
    (fun x y => hg (x,y)) w s

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
