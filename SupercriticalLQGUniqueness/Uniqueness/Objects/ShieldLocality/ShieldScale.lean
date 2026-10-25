import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Block
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.ScaleGood
import LQGMetric.Field.GermSplitA




 






set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality

 
theorem shieldAt_iff_of_dist_scale (C : Objects.CorrectedEvent.Constants)
    (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (t : ℝ) :
    Objects.Excursions.shieldAt C E t ↔ Objects.Excursions.shieldAt C D t := by
  rw [Objects.Excursions.shieldAt, Objects.Excursions.shieldAt,
    Objects.ProbabilityS3.around_eq_mul_of_dist_scale D E c hc0 hcTop hscale,
    Objects.ProbabilityS3.acr_eq_mul_of_dist_scale D E c hc0 hcTop hscale]
  have hfin (x : ℝ≥0∞) : (c * x < ⊤) ↔ (x < ⊤) := by
    constructor
    · intro hx
      exact ENNReal.lt_top_of_mul_ne_top_right hx.ne hc0
    · intro hx
      exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hcTop) hx
  rw [hfin, mul_left_comm (ENNReal.ofReal C.lamConst) c,
    ENNReal.mul_le_mul_iff_right hc0 hcTop]

 
theorem shield_iff_of_dist_scale (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData)
    (Ksh : ℕ) (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) :
    Objects.Excursions.shield C T Ksh E ↔ Objects.Excursions.shield C T Ksh D := by
  simp only [Objects.Excursions.shield]
  exact exists_congr fun k => and_congr_right fun _ =>
    shieldAt_iff_of_dist_scale C D E c hc0 hcTop hscale _

 
theorem ae_shieldAt_addConst_iff
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (t : ℝ) (c : LQGMetric.DistC → ℝ) :
    ∀ᵐ g ∂μ,
      Objects.Excursions.shieldAt C (D (LQGMetric.addConst g (c g))) t ↔
        Objects.Excursions.shieldAt C (D g) t := by
  have hwhole : LQGMetric.IsGFFPlusCont
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD c] with g hg
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c g))
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heTop : e ≠ ∞ := ENNReal.ofReal_ne_top
  exact shieldAt_iff_of_dist_scale C (D g)
    (D (LQGMetric.addConst g (c g))) e he0 heTop
    (fun x y => hg (x, y)) t

 
theorem ae_shield_addConst_iff
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (c : LQGMetric.DistC → ℝ) :
    ∀ᵐ g ∂μ,
      Objects.Excursions.shield C T Ksh (D (LQGMetric.addConst g (c g))) ↔
        Objects.Excursions.shield C T Ksh (D g) := by
  have hwhole : LQGMetric.IsGFFPlusCont
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  filter_upwards [Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD c] with g hg
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c g))
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heTop : e ≠ ∞ := ENNReal.ofReal_ne_top
  exact shield_iff_of_dist_scale C T Ksh (D g)
    (D (LQGMetric.addConst g (c g))) e he0 heTop
    (fun x y => hg (x, y))

end SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality
