import SupercriticalLQGUniqueness.B2.DG20Lim.AnnulusPathHit
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleMinimizers
import LQGMetric.Metric.CurveLength

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finiteCircleDist_le_crossing_paths_around
    (D : LQGMetric.ContMetric) (A : RatAnnulus)
    (O₁ O₁' O₂ O₂' : RatCircle)
    (h₁ : A.OppositeSides O₁ O₁')
    (h₂ : A.OppositeSides O₂ O₂')
    {γ₁ γ₂ : ℝ → D.Space} {a₁ b₁ a₂ b₂ : ℝ}
    (hab₁ : a₁ ≤ b₁) (hab₂ : a₂ ≤ b₂)
    (hc₁ : ContinuousOn γ₁ (Icc a₁ b₁))
    (hc₂ : ContinuousOn γ₂ (Icc a₂ b₂))
    {u₁ v₁ u₂ v₂ : ℂ}
    (hu₁ : u₁ ∈ O₁.toSet) (hv₁ : v₁ ∈ O₁'.toSet)
    (hu₂ : u₂ ∈ O₂.toSet) (hv₂ : v₂ ∈ O₂'.toSet)
    (hga₁ : γ₁ a₁ = D.pt u₁) (hgb₁ : γ₁ b₁ = D.pt v₁)
    (hga₂ : γ₂ a₂ = D.pt u₂) (hgb₂ : γ₂ b₂ = D.pt v₂)
    {G : ℝ → ℂ} {c d : ℝ}
    (hG : LQGMetric.Disconnects (G '' Icc c d)
      A.inner.toSet A.outer.toSet) :
    LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
      LQGMetric.MetricGeometry.curveLength γ₁ a₁ b₁ +
        D.len G c d + LQGMetric.MetricGeometry.curveLength γ₂ a₂ b₂ := by
  let q₁ : ℝ → ℂ := fun t => D.unpt (γ₁ t)
  let q₂ : ℝ → ℂ := fun t => D.unpt (γ₂ t)
  have hq₁ : ContinuousOn q₁ (Icc a₁ b₁) := D.continuous_unpt.comp_continuousOn hc₁
  have hq₂ : ContinuousOn q₂ (Icc a₂ b₂) := D.continuous_unpt.comp_continuousOn hc₂
  have hqa₁ : q₁ a₁ = u₁ := by simp [q₁, hga₁]
  have hqb₁ : q₁ b₁ = v₁ := by simp [q₁, hgb₁]
  have hqa₂ : q₂ a₂ = u₂ := by simp [q₂, hga₂]
  have hqb₂ : q₂ b₂ = v₂ := by simp [q₂, hgb₂]
  obtain ⟨t₁, ht₁, s₁, hs₁, heq₁⟩ :=
    A.exists_hit_around_of_opposite_sides O₁ O₁' h₁ hab₁ hq₁
      (hqa₁ ▸ hu₁) (hqb₁ ▸ hv₁) hG
  obtain ⟨t₂, ht₂, s₂, hs₂, heq₂⟩ :=
    A.exists_hit_around_of_opposite_sides O₂ O₂' h₂ hab₂ hq₂
      (hqa₂ ▸ hu₂) (hqb₂ ▸ hv₂) hG
  have hpt₁ : D.pt (G s₁) = γ₁ t₁ := by
    calc
      D.pt (G s₁) = D.pt (q₁ t₁) := by rw [← heq₁]
      _ = γ₁ t₁ := by simp [q₁]
  have hpt₂ : D.pt (G s₂) = γ₂ t₂ := by
    calc
      D.pt (G s₂) = D.pt (q₂ t₂) := by rw [← heq₂]
      _ = γ₂ t₂ := by simp [q₂]
  have hloop : edist (γ₁ t₁) (γ₂ t₂) ≤ D.len G c d := by
    rw [← hpt₁, ← hpt₂, LQGMetric.ContMetric.edist_pt]
    exact LQGMetric.GM.ofReal_dist_le_len D hs₁ hs₂
  have hset : LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
      edist (D.pt u₁) (D.pt u₂) := by
    unfold LQGMetric.Blueprint.setDist
    exact LQGMetric.MetricGeometry.setEDist_le_edist
      (Set.mem_image_of_mem D.pt hu₁) (Set.mem_image_of_mem D.pt hu₂)
  calc
    _ ≤ edist (D.pt u₁) (D.pt u₂) := hset
    _ = edist (γ₁ a₁) (γ₂ a₂) := by rw [hga₁, hga₂]
    _ ≤ edist (γ₁ a₁) (γ₁ t₁) + edist (γ₁ t₁) (γ₂ t₂) +
        edist (γ₂ t₂) (γ₂ a₂) := by
      calc
        _ ≤ edist (γ₁ a₁) (γ₁ t₁) + edist (γ₁ t₁) (γ₂ a₂) :=
          edist_triangle _ _ _
        _ ≤ edist (γ₁ a₁) (γ₁ t₁) +
            (edist (γ₁ t₁) (γ₂ t₂) + edist (γ₂ t₂) (γ₂ a₂)) := by
          gcongr
          exact edist_triangle _ _ _
        _ = _ := by ac_rfl
    _ ≤ LQGMetric.MetricGeometry.curveLength γ₁ a₁ t₁ + D.len G c d +
        LQGMetric.MetricGeometry.curveLength γ₂ a₂ t₂ := by
      have hleft := LQGMetric.MetricGeometry.edist_le_curveLength γ₁ ht₁.1
      have hright : edist (γ₂ t₂) (γ₂ a₂) ≤
          LQGMetric.MetricGeometry.curveLength γ₂ a₂ t₂ := by
        rw [edist_comm]
        exact LQGMetric.MetricGeometry.edist_le_curveLength γ₂ ht₂.1
      exact add_le_add (add_le_add hleft hloop) hright
    _ ≤ _ := by
      exact add_le_add
        (add_le_add
          (LQGMetric.MetricGeometry.curveLength_mono γ₁ le_rfl ht₁.2) le_rfl)
        (LQGMetric.MetricGeometry.curveLength_mono γ₂ le_rfl ht₂.2)

end SupercriticalLQGUniqueness.B2.DG20Lim
