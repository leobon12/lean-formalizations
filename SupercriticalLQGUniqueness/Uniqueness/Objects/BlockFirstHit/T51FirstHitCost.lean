import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockFirstHit.T51FirstHit
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh.InternalShortcut




 





set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockFirstHit

theorem annulus_internal_le_ball_path_len
    (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hcont : ContinuousOn P (Icc a b))
    {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ < r₂)
    (ha : dist (P a) c = r₂) (hb : dist (P b) c ≤ r₁)
    (hball : MapsTo P (Icc a b) (closedBall c r₂)) :
    ∃ t : ℝ, ∃ (hat : P a ∈ closedBall c r₂ \ ball c r₁)
      (htt : P t ∈ closedBall c r₂ \ ball c r₁),
      a ≤ t ∧ t ≤ b ∧ P t ∈ sphere c r₁ ∧
        D.internal (closedBall c r₂ \ ball c r₁) (⟨P a, hat⟩, ⟨P t, htt⟩) ≤
          D.len P a b := by
  obtain ⟨t, hat, htb, hts, hprefix⟩ :=
    first_inner_hit_prefix hP.1 hcont hr ha hb hball
  let K : Set ℂ := closedBall c r₂ \ ball c r₁
  have hKa : P a ∈ K := hprefix (left_mem_Icc.mpr hat)
  have hKt : P t ∈ K := hprefix (right_mem_Icc.mpr hat)
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl htb
  have hcurve : D.IsCurve P a t := ⟨hat, hP.2.mono hsub⟩
  have hcost : D.internal K (⟨P a, hKa⟩, ⟨P t, hKt⟩) ≤ D.len P a t := by
    rw [D.internal_eq_internalEDist]
    exact TwoScale.Mesh.internal_trace_le_len D K P hcurve hprefix
      ⟨a, left_mem_Icc.mpr hat, rfl⟩ ⟨t, right_mem_Icc.mpr hat, rfl⟩
  exact ⟨t, hKa, hKt, hat, htb, hts,
    hcost.trans (eVariationOn.mono _ hsub)⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockFirstHit
