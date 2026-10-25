import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths.T51Truncate
import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 





set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths

theorem acr_le_len_of_inner_outer_path
    (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hcont : ContinuousOn P (Icc a b))
    {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    (ha : ‖P a - c‖ ≤ r₁) (hb : r₂ ≤ ‖P b - c‖) :
    Objects.CorrectedEvent.acr D c r₁ r₂ ≤ D.len P a b := by
  obtain ⟨s, t, has, hst, htb, hs, ht, htrace⟩ :=
    first_outer_last_inner_closed_annulus hP.1 hcont hr ha hb
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hcurve : D.IsCurve P s t := ⟨hst, hP.2.mono hsub⟩
  have htrace' : P '' Icc s t ⊆ Objects.CorrectedEvent.cann c r₁ r₂ := by
    rintro x ⟨u, hu, rfl⟩
    have hh := htrace hu
    exact ⟨le_of_not_gt (fun h => hh.2 (mem_ball.mpr h)),
      mem_closedBall.mp hh.1⟩
  calc
    Objects.CorrectedEvent.acr D c r₁ r₂ ≤ D.len P s t := by
      unfold Objects.CorrectedEvent.acr
      exact iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t
        (iInf_le_of_le hcurve (iInf_le_of_le htrace'
          (iInf_le_of_le hs (iInf_le _ ht))))))
    _ ≤ D.len P a b := eVariationOn.mono _ hsub


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths
