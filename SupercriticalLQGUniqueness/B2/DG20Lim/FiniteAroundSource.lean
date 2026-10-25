import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAroundPath

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finiteCircleDist_le_across_across_around
    (D : LQGMetric.ContMetric) (hD : D.IsLength)
    (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle)
    (h₁ : A.OppositeSides O₁ O₁')
    (h₂ : A.OppositeSides O₂ O₂') :
    LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
      LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet +
        LQGMetric.Blueprint.setDist D O₂.toSet O₂'.toSet +
          D.aroundDist A.toSet A.inner.toSet A.outer.toSet := by
  let C : ℝ≥0∞ := LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet +
    LQGMetric.Blueprint.setDist D O₂.toSet O₂'.toSet
  change LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
    C + D.aroundDist A.toSet A.inner.toSet A.outer.toSet
  simp only [LQGMetric.ContMetric.aroundDist, ENNReal.add_iInf]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun G =>
    le_iInf fun hab => le_iInf fun hcont => le_iInf fun hsub =>
      le_iInf fun hdisc => ?_
  exact finiteCircleDist_le_across_across_aroundPath D hD A
    O₁ O₁' O₂ O₂' h₁ h₂ hdisc

end SupercriticalLQGUniqueness.B2.DG20Lim
