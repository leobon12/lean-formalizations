import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.BoundaryTranslate




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem ae_normalized_boundary_translate
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (c w : ℂ) (hw : w ≠ 0) :
    ∀ᵐ ω ∂P,
      (D (h ω)).internal (Metric.closedBall c ‖w‖)
          (⟨w + c, by simp only [Metric.mem_closedBall, dist_eq_norm,
              add_sub_cancel_right, le_refl]⟩,
           ⟨c, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
        Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ c =
      (D (TwoScale.S36.recentredTranslate h c ω)).internal (Metric.closedBall 0 ‖w‖)
          (⟨w, by simp only [Metric.mem_closedBall, dist_zero_right, le_refl]⟩,
           ⟨0, Metric.mem_closedBall_self (norm_nonneg w)⟩) /
        Objects.AnnulusTails.nrm ξ Q (TwoScale.S36.recentredTranslate h c ω) ‖w‖ 0 := by
  have hplus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hh.1
  have htrGFF : LQGMetric.IsWholePlaneGFF
      (fun ω => translateDist c (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using
      hh.1.affineComp one_pos c
  have hplusTr : LQGMetric.IsGFFPlusCont
      (fun ω => translateDist c (h ω)) P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp htrGFF
  let s : Set.Ioi (0 : ℝ) := ⟨‖w‖, norm_pos_iff.mpr hw⟩
  filter_upwards [hD.translation P h hplus c,
    Positivity.Witnesses.ae_addConst_eq_mul P (fun ω => translateDist c (h ω)) hplusTr
      ξ Q D hD (fun ω => -LQGMetric.circleAvg (h ω) 1 c),
    ae_circleAvg_normalized_translate hh c s] with ω hT hW hAvg
  let t : ℝ := -LQGMetric.circleAvg (h ω) 1 c
  let k : ENNReal := ENNReal.ofReal (Real.exp ((ξ : ℝ) * t))
  have hk0 : k ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkt : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hm (x y : ℂ) :
      D (TwoScale.S36.recentredTranslate h c ω) (x - c, y - c) =
        k * D (h ω) (x, y) := by
    rw [TwoScale.S36.recentredTranslate, hW (x - c, y - c)]
    dsimp only [k, t]
    rw [hT (x - c) (y - c), sub_add_cancel, sub_add_cancel]
  have hInt := boundaryInternal_translate_scale
    (D (h ω)) (D (TwoScale.S36.recentredTranslate h c ω)) c w k hk0 hkt hm
  have hN :
      Objects.AnnulusTails.nrm ξ Q (TwoScale.S36.recentredTranslate h c ω) ‖w‖ 0 =
        k * Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ c := by
    unfold Objects.AnnulusTails.nrm
    change ENNReal.ofReal
      (‖w‖ ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) *
          LQGMetric.circleAvg (TwoScale.S36.recentredTranslate h c ω) ‖w‖ 0)) =
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * t)) *
        ENNReal.ofReal
          (‖w‖ ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * LQGMetric.circleAvg (h ω) ‖w‖ c))
    rw [show LQGMetric.circleAvg (TwoScale.S36.recentredTranslate h c ω) ‖w‖ 0 =
        LQGMetric.circleAvg (h ω) ‖w‖ c + t by
          simpa only [TwoScale.S36.recentredTranslate, s, t, sub_eq_add_neg] using hAvg]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [mul_add, Real.exp_add]
    ring
  rw [hInt, hN]
  exact (ENNReal.mul_div_mul_left _ _ hk0 hkt).symm


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
