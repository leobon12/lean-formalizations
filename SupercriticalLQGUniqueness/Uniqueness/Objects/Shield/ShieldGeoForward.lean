import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldFullProb




set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

 

theorem internal_le_of_compact_geodesic
    (D : LSCMetric) (K : Set ℂ) (u v : K)
    (P : ℝ → ℂ) (a b : ℝ)
    (hP : D.IsCurve P a b)
    (htrace : ∀ t ∈ Icc a b, P t ∈ K)
    (hu : P a = (u : ℂ)) (hv : P b = (v : ℂ))
    (hlen : D.len P a b = D ((u : ℂ), (v : ℂ))) :
    D.internal K (u, v) ≤ D ((u : ℂ), (v : ℂ)) := by
  unfold LSCMetric.internal
  calc
    _ ≤ D.len P a b := by
      apply iInf_le_of_le P
      apply iInf_le_of_le a
      apply iInf_le_of_le b
      apply iInf_le_of_le hP
      apply iInf_le_of_le htrace
      apply iInf_le_of_le hu
      exact iInf_le_of_le hv le_rfl
    _ = _ := hlen

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
