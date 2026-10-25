import SupercriticalLQGUniqueness.B2.DG20Lim.AnnulusPathBound

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finiteCircleDist_le_across_across_aroundPath
    (D : LQGMetric.ContMetric) (hD : D.IsLength)
    (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle)
    (h₁ : A.OppositeSides O₁ O₁')
    (h₂ : A.OppositeSides O₂ O₂')
    {G : ℝ → ℂ} {c d : ℝ}
    (hG : LQGMetric.Disconnects (G '' Icc c d)
      A.inner.toSet A.outer.toSet) :
    LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
      LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet +
        LQGMetric.Blueprint.setDist D O₂.toSet O₂'.toSet + D.len G c d := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ : NNReal := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨u₁, hu₁, v₁, hv₁, hmin₁⟩ := exists_circleDist_minimizers D O₁ O₁'
  obtain ⟨u₂, hu₂, v₂, hv₂, hmin₂⟩ := exists_circleDist_minimizers D O₂ O₂'
  obtain ⟨γ₁, a₁, b₁, hab₁, hc₁, hga₁, hgb₁, hlen₁⟩ :=
    (LQGMetric.MetricGeometry.isLengthSpace_iff_curves).1 hD
      (D.pt u₁) (D.pt v₁) δ (by exact_mod_cast hδ)
  obtain ⟨γ₂, a₂, b₂, hab₂, hc₂, hga₂, hgb₂, hlen₂⟩ :=
    (LQGMetric.MetricGeometry.isLengthSpace_iff_curves).1 hD
      (D.pt u₂) (D.pt v₂) δ (by exact_mod_cast hδ)
  have hpath := finiteCircleDist_le_crossing_paths_around D A
    O₁ O₁' O₂ O₂' h₁ h₂ hab₁ hab₂ hc₁ hc₂
    hu₁ hv₁ hu₂ hv₂ hga₁ hgb₁ hga₂ hgb₂ hG
  have hlen₁' : LQGMetric.MetricGeometry.curveLength γ₁ a₁ b₁ ≤
      LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet + (δ : ℝ≥0∞) := by
    simpa only [LQGMetric.ContMetric.edist_pt,
      ENNReal.ofReal_coe_nnreal, ← hmin₁] using hlen₁
  have hlen₂' : LQGMetric.MetricGeometry.curveLength γ₂ a₂ b₂ ≤
      LQGMetric.Blueprint.setDist D O₂.toSet O₂'.toSet + (δ : ℝ≥0∞) := by
    simpa only [LQGMetric.ContMetric.edist_pt,
      ENNReal.ofReal_coe_nnreal, ← hmin₂] using hlen₂
  calc
    _ ≤ LQGMetric.MetricGeometry.curveLength γ₁ a₁ b₁ +
        D.len G c d + LQGMetric.MetricGeometry.curveLength γ₂ a₂ b₂ := hpath
    _ ≤ (LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet + (δ : ℝ≥0∞)) +
        D.len G c d +
        (LQGMetric.Blueprint.setDist D O₂.toSet O₂'.toSet + (δ : ℝ≥0∞)) :=
      add_le_add (add_le_add hlen₁' le_rfl) hlen₂'
    _ = LQGMetric.Blueprint.setDist D O₁.toSet O₁'.toSet +
        LQGMetric.Blueprint.setDist D O₂.toSet O₂'.toSet + D.len G c d + ε := by
      have hδδ : (δ : ℝ≥0∞) + (δ : ℝ≥0∞) = (ε : ℝ≥0∞) := by
        norm_num [δ]
      rw [← hδδ]
      ac_rfl

end SupercriticalLQGUniqueness.B2.DG20Lim
