import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldModConst
import LQGMetric.Papers.CONF.S3D110A




 






set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

 

theorem aeEventIn_shieldAt_recentered
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (t : ℝ) (ht : 0 < t) :
    AEEventIn μ
      (fieldSigma
        (fun g : LQGMetric.DistC =>
          LQGMetric.addConst g (-LQGMetric.circleAvg g ((22 / 5) * t) 0))
        (Objects.ShieldLocality.shieldWindow t))
      {g | Objects.Excursions.shieldAt C (D g) t} := by
  obtain ⟨R, hR, hEq⟩ :=
    Objects.ShieldLocality.aeEventIn_shieldAt_modConst_open μ hμ ξ Q D hD C t ht
  refine ⟨R, ?_, hEq⟩
  have hSigma := LQGMetric.CONF.fieldSigma0On_addConst
    (id : LQGMetric.DistC → LQGMetric.DistC)
    (fun g => -LQGMetric.circleAvg g ((22 / 5) * t) 0)
    (Objects.ShieldLocality.shieldWindow t : Set ℂ)
  rw [← hSigma] at hR
  exact LQGMetric.CONF.fieldSigma0On_le_fieldSigma _
    (Objects.ShieldLocality.shieldWindow t).isOpen R hR

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
