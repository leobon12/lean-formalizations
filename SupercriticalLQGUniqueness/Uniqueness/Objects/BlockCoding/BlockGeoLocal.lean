import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.CompactAttain
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal




 


set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

 

theorem compact_geodesic_congr (D E : LSCMetric) (K : Set ℂ)
    (hK : IsCompact K) (u v : K)
    (hint : D.internal K (u, v) = E.internal K (u, v))
    (hamb : D ((u : ℂ), (v : ℂ)) = E ((u : ℂ), (v : ℂ))) :
    ((∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
      (∀ s ∈ Icc a b, P s ∈ K) ∧
      P a = (u : ℂ) ∧ P b = (v : ℂ) ∧
      D.len P a b = D ((u : ℂ), (v : ℂ))) ∧
      D ((u : ℂ), (v : ℂ)) < ⊤) ↔
    ((∃ (P : ℝ → ℂ) (a b : ℝ), E.IsCurve P a b ∧
      (∀ s ∈ Icc a b, P s ∈ K) ∧
      P a = (u : ℂ) ∧ P b = (v : ℂ) ∧
      E.len P a b = E ((u : ℂ), (v : ℂ))) ∧
      E ((u : ℂ), (v : ℂ)) < ⊤) := by
  rw [compact_geodesic_iff_internal D hK u v,
    compact_geodesic_iff_internal E hK u v, hint, hamb]

 

theorem compact_geodesic_congr_window (D E : LSCMetric) (K W : Set ℂ)
    (hK : IsCompact K) (hKW : K ⊆ W) (hEq : D.internal W = E.internal W)
    (u v : K)
    (hamb : D ((u : ℂ), (v : ℂ)) = E ((u : ℂ), (v : ℂ))) :
    ((∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧
      (∀ s ∈ Icc a b, P s ∈ K) ∧
      P a = (u : ℂ) ∧ P b = (v : ℂ) ∧
      D.len P a b = D ((u : ℂ), (v : ℂ))) ∧
      D ((u : ℂ), (v : ℂ)) < ⊤) ↔
    ((∃ (P : ℝ → ℂ) (a b : ℝ), E.IsCurve P a b ∧
      (∀ s ∈ Icc a b, P s ∈ K) ∧
      P a = (u : ℂ) ∧ P b = (v : ℂ) ∧
      E.len P a b = E ((u : ℂ), (v : ℂ))) ∧
      E ((u : ℂ), (v : ℂ)) < ⊤) := by
  apply compact_geodesic_congr D E K hK u v _ hamb
  exact congrFun (Toolkit.InternalMetrics.internal_eq_of_internal_eq D E hKW hEq) (u, v)

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
