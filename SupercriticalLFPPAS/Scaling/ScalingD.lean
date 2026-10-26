import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLQGUniqueness.B2.Strong.Bridge
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Field.GFFLaw

/-! # Scaling covariance of the limiting metric

The paper's identity (1.3), obtained from Axiom IV and Weyl scaling. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal
open LQGMetric (DistC IsWholePlaneGFF IsGFFPlusCont addConst affineComp circleAvg)
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF scaleTranslateDist)

namespace SupercriticalLFPPAS.Scaling

theorem scalingD_holds (S : Core.Setup) : Core.ScalingDStmt S := by
  intro Ω _ P _ h hh r z
  have hAffine : IsWholePlaneGFF (fun ω => affineComp (r : ℝ) z (h ω)) P :=
    hh.1.affineComp r.2 z
  have hRec : IsNormalizedWholePlaneGFF (fun ω => Core.recentred r z (h ω)) P := by
    apply SupercriticalLQGUniqueness.isNormalizedWholePlaneGFF_iff_old.mpr
    have hc : Measurable (fun ω => -circleAvg (h ω) r z) :=
      ((LQGMetric.measurable_circleAvg_left r z).comp hh.1.measurable).neg
    have hRecWhole : IsWholePlaneGFF (fun ω => Core.recentred r z (h ω)) P := by
      have h' := hAffine.addConst hc
      simpa only [Core.recentred, SupercriticalLQGUniqueness.B2.Strong.scaleTranslateDist_eq_affineComp]
        using h'
    have hRecNorm : ∀ᵐ ω ∂P, circleAvg (Core.recentred r z (h ω)) 1 0 = 0 := by
      filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hAffine,
        LQGMetric.CircleAvg.ae_circleAvg_affineComp hh.1 r.2 z] with ω hca hsc
      rw [Core.recentred, SupercriticalLQGUniqueness.B2.Strong.scaleTranslateDist_eq_affineComp]
      rw [hca, hsc]
      ring
    exact ⟨hRecWhole, hRecNorm⟩
  have hRecPlus : IsGFFPlusCont (fun ω => Core.recentred r z (h ω)) P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hRec.1
  have hIV := S.hD.2.2.2.2.1 P h
    (LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1) r z
  have hW := SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul
    P (fun ω => Core.recentred r z (h ω)) hRecPlus S.ξ S.Q S.D
    (SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric S.hD)
    (fun ω => circleAvg (h ω) r z + S.Q * Real.log (r : ℝ))
  have hExp (c : ℝ) :
      Real.exp ((S.ξ : ℝ) * (c + S.Q * Real.log (r : ℝ))) =
        (r : ℝ) ^ ((S.ξ : ℝ) * S.Q) * Real.exp ((S.ξ : ℝ) * c) := by
    calc
      Real.exp ((S.ξ : ℝ) * (c + S.Q * Real.log (r : ℝ))) =
          Real.exp ((S.ξ : ℝ) * c + ((S.ξ : ℝ) * S.Q) * Real.log (r : ℝ)) := by
            congr 1
            ring
      _ = Real.exp ((S.ξ : ℝ) * c) *
          Real.exp (((S.ξ : ℝ) * S.Q) * Real.log (r : ℝ)) := Real.exp_add _ _
      _ = Real.exp ((S.ξ : ℝ) * c) * (r : ℝ) ^ ((S.ξ : ℝ) * S.Q) := by
            rw [show ((S.ξ : ℝ) * S.Q) * Real.log (r : ℝ) =
              Real.log (r : ℝ) * ((S.ξ : ℝ) * S.Q) by ring,
              ← Real.rpow_def_of_pos r.2]
      _ = _ := mul_comm _ _
  refine ⟨hRec, ?_⟩
  filter_upwards [hIV, hW] with ω hIVω hWω
  intro u v
  have hfield :
      addConst (scaleTranslateDist r z (h ω)) (S.Q * Real.log (r : ℝ)) =
        addConst (Core.recentred r z (h ω))
          (circleAvg (h ω) r z + S.Q * Real.log (r : ℝ)) := by
    rw [Core.recentred, LQGMetric.GFFLaw.addConst_addConst]
    congr 1
    ring
  calc
    S.D (h ω) (z + (r : ℝ) • u, z + (r : ℝ) • v) =
        S.D (addConst (scaleTranslateDist r z (h ω)) (S.Q * Real.log (r : ℝ))) (u, v) := by
          simpa only [add_comm] using hIVω u v
    _ = S.D (addConst (Core.recentred r z (h ω))
          (circleAvg (h ω) r z + S.Q * Real.log (r : ℝ))) (u, v) := by rw [hfield]
    _ = ENNReal.ofReal ((r : ℝ) ^ ((S.ξ : ℝ) * S.Q) *
          Real.exp ((S.ξ : ℝ) * circleAvg (h ω) r z)) *
        S.D (Core.recentred r z (h ω)) (u, v) := by
          rw [hWω (u, v), hExp]

end SupercriticalLFPPAS.Scaling
