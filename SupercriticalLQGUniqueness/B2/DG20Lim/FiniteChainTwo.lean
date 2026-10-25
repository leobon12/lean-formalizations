import SupercriticalLQGUniqueness.B2.DG20Lim.CircleMinimizers
import LQGMetric.Papers.GM.S3.AttainedShortcut
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit

 


set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finiteCircleDist_two_chain (D : LQGMetric.ContMetric)
    (hD : D.IsLength) (O₀ O₁ O₂ : RatCircle)
    (hsep : Disconnects O₁.toSet O₀.toSet O₂.toSet) :
    LQGMetric.Blueprint.setDist D O₀.toSet O₁.toSet +
      LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
      LQGMetric.Blueprint.setDist D O₀.toSet O₂.toSet := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨u, hu, v, hv, hmin⟩ := exists_circleDist_minimizers D O₀ O₂
  obtain ⟨γ, a, b, hab, hγ, hga, hgb, hlen⟩ :=
    (LQGMetric.MetricGeometry.isLengthSpace_iff_curves).1 hD
      (D.pt u) (D.pt v) ε (by exact_mod_cast hε)
  let q : ℝ → ℂ := fun t => D.unpt (γ t)
  have hq : ContinuousOn q (Icc a b) := D.continuous_unpt.comp_continuousOn hγ
  have hqa : q a = u := by simp [q, hga]
  have hqb : q b = v := by simp [q, hgb]
  obtain ⟨t, ht, hqt⟩ :=
    LQGMetric.GM.exists_hit_of_disconnects hab hq
      (Uniqueness.Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep)
      (by simpa only [hqa] using hu) (by simpa only [hqb] using hv)
  have hleft : LQGMetric.Blueprint.setDist D O₀.toSet O₁.toSet ≤
      LQGMetric.MetricGeometry.curveLength γ a t := by
    have hset : LQGMetric.Blueprint.setDist D O₀.toSet O₁.toSet ≤
        edist (γ a) (γ t) := by
      unfold LQGMetric.Blueprint.setDist
      apply LQGMetric.MetricGeometry.setEDist_le_edist
      · exact ⟨u, hu, by simp [hga]⟩
      · exact ⟨q t, hqt, by simp [q]⟩
    exact hset.trans (LQGMetric.MetricGeometry.edist_le_curveLength γ ht.1)
  have hright : LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
      LQGMetric.MetricGeometry.curveLength γ t b := by
    have hset : LQGMetric.Blueprint.setDist D O₁.toSet O₂.toSet ≤
        edist (γ t) (γ b) := by
      unfold LQGMetric.Blueprint.setDist
      apply LQGMetric.MetricGeometry.setEDist_le_edist
      · exact ⟨q t, hqt, by simp [q]⟩
      · exact ⟨v, hv, by simp [hgb]⟩
    exact hset.trans (LQGMetric.MetricGeometry.edist_le_curveLength γ ht.2)
  calc
    _ ≤ LQGMetric.MetricGeometry.curveLength γ a t +
        LQGMetric.MetricGeometry.curveLength γ t b := add_le_add hleft hright
    _ = LQGMetric.MetricGeometry.curveLength γ a b :=
      LQGMetric.MetricGeometry.curveLength_add γ ht.1 ht.2
    _ ≤ edist (D.pt u) (D.pt v) + ENNReal.ofReal ε := hlen
    _ = LQGMetric.Blueprint.setDist D O₀.toSet O₂.toSet + ε := by
      rw [LQGMetric.ContMetric.edist_pt, ENNReal.ofReal_coe_nnreal, ← hmin]

end SupercriticalLQGUniqueness.B2.DG20Lim
