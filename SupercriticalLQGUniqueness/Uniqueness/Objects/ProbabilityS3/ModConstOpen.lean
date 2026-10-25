import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.BarrierScale
import LQGMetric.Field.GermSplitA




 


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

private theorem regWindow_nonempty (w : ℂ) (s : ℝ) (hs : 0 < s) :
    (regWindow w s : Set ℂ).Nonempty := by
  refine ⟨w + (s : ℂ), ?_⟩
  change (7/8)*s < ‖w + (s : ℂ) - w‖ ∧
    ‖w + (s : ℂ) - w‖ < (17/8)*s
  simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  constructor <;> nlinarith only [hs]

theorem aeEventIn_regGood_modConst_open
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (w : ℂ) (s : ℝ) (hs : 0 < s) :
    AEEventIn μ (fieldSigma0On id (regWindow w s))
      {g | Objects.CorrectedEvent.regGood C (D g) s w} := by
  let U := regWindow w s
  obtain ⟨ψ, hψU, hψ1⟩ :=
    LQGMetric.GermSplit.exists_test_unit (regWindow_nonempty w s hs)
  have hwhole : LQGMetric.IsGFFPlusCont
      (id : LQGMetric.DistC → LQGMetric.DistC) μ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hμ.1
  let G := LQGMetric.CONF.normIn (id : LQGMetric.DistC → LQGMetric.DistC) ψ
  have hG : LQGMetric.IsGFFPlusCont G μ :=
    Toolkit.LocalEvents.isGFFPlusCont_normIn hwhole ψ
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hB := BiLipschitz.Barrier.ae_barrier hD hQ μ id hμ
  have hscale := Positivity.Witnesses.ae_addConst_eq_mul μ id hwhole ξ Q D hD
    (fun g => -(g ψ))
  have hBG : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D (G g)) := by
    filter_upwards [hB, hscale] with g hb hc
    let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * -(g ψ)))
    exact barrier_of_dist_scale (D g) (D (G g)) e
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top (fun x y => hc (x,y)) hb
  have hLocal := aeEventIn_regGood_open_of_barrier μ G hG ξ Q D hD hBG C w s hs
    U (closedAnn_subset_regWindow w s hs) (annulus_subset_regWindow w s hs)
  have hLocal0 := Toolkit.LocalEvents.aeEventIn_fieldSigma0On_of_normIn
    (id : LQGMetric.DistC → LQGMetric.DistC) ψ hψ1 U hψU hLocal
  have hEq := ae_regGood_addConst_iff μ hμ ξ Q D hD C w s
    (fun g => -(g ψ))
  obtain ⟨R, hRm, hGR⟩ := hLocal0
  refine ⟨R, hRm, ?_⟩
  filter_upwards [hEq, hGR] with g he hR
  exact propext (he.symm.trans (Iff.of_eq hR))

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
