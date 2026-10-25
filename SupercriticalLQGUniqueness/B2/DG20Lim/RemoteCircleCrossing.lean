import SupercriticalLQGUniqueness.B2.DG20Lim.CircleCrossing

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem setDist_nested_circles_le_pointDist (D : LQGMetric.ContMetric)
    (hD : D.IsLength) (O P : RatCircle)
    (hOP : P.SurroundsCircle O) {x y : ℂ}
    (hx : x ∈ O.openDisk) (hy : y ∈ P.closedDiskᶜ) :
    LQGMetric.Blueprint.setDist D O.toSet P.toSet ≤
      ENNReal.ofReal (D.1 (x, y)) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨γ, a, b, hab, hγ, hga, hgb, hlen⟩ :=
    (LQGMetric.MetricGeometry.isLengthSpace_iff_curves).1 hD
      (D.pt x) (D.pt y) ε (by exact_mod_cast hε)
  let q : ℝ → ℂ := fun t => D.unpt (γ t)
  have hq : ContinuousOn q (Icc a b) :=
    D.continuous_unpt.comp_continuousOn hγ
  have hqa : q a = x := by simp [q, hga]
  have hqb : q b = y := by simp [q, hgb]
  have hPstart : dist x P.center < (P.radius : ℝ) :=
    mem_ball.mp (hOP.2 (O.openDisk_subset_closedDisk hx))
  have hPend : (P.radius : ℝ) < dist y P.center := by
    simpa only [RatCircle.closedDisk, mem_compl_iff, mem_closedBall, not_le] using hy
  have hcontP : ContinuousOn (fun t => dist (q t) P.center) (Icc a b) :=
    (continuous_id.dist continuous_const).comp_continuousOn hq
  obtain ⟨tP, htP, htPval⟩ := (isPreconnected_Icc.intermediate_value
      (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hcontP)
    (show (P.radius : ℝ) ∈ Icc (dist (q a) P.center) (dist (q b) P.center) by
      rw [hqa, hqb]
      exact ⟨hPstart.le, hPend.le⟩)
  have htPmem : q tP ∈ P.toSet := mem_sphere.mpr htPval
  have hOstart : dist x O.center < (O.radius : ℝ) := mem_ball.mp hx
  have hOend : (O.radius : ℝ) < dist (q tP) O.center := by
    have hpo : q tP ∉ O.closedDisk := by
      intro hpo
      have hPin : q tP ∈ P.openDisk := hOP.2 hpo
      have hPnot : q tP ∉ P.openDisk := by
        simpa only [RatCircle.openDisk, mem_ball, not_lt, htPval] using
          (le_refl (P.radius : ℝ))
      exact hPnot hPin
    simpa only [RatCircle.closedDisk, mem_closedBall, not_le] using hpo
  have hcontO : ContinuousOn (fun t => dist (q t) O.center) (Icc a tP) :=
    ((continuous_id.dist continuous_const).comp_continuousOn hq).mono
      (Icc_subset_Icc le_rfl htP.2)
  obtain ⟨tO, htO, htOval⟩ := (isPreconnected_Icc.intermediate_value
      (left_mem_Icc.mpr htP.1) (right_mem_Icc.mpr htP.1) hcontO)
    (show (O.radius : ℝ) ∈ Icc (dist (q a) O.center) (dist (q tP) O.center) by
      rw [hqa]
      exact ⟨hOstart.le, hOend.le⟩)
  have htOmem : q tO ∈ O.toSet := mem_sphere.mpr htOval
  have hset : LQGMetric.Blueprint.setDist D O.toSet P.toSet ≤
      edist (γ tO) (γ tP) := by
    unfold LQGMetric.Blueprint.setDist
    apply LQGMetric.MetricGeometry.setEDist_le_edist
    · exact ⟨q tO, htOmem, by simp [q]⟩
    · exact ⟨q tP, htPmem, by simp [q]⟩
  calc
    LQGMetric.Blueprint.setDist D O.toSet P.toSet ≤ edist (γ tO) (γ tP) := hset
    _ ≤ LQGMetric.MetricGeometry.curveLength γ tO tP :=
      LQGMetric.MetricGeometry.edist_le_curveLength γ htO.2
    _ ≤ LQGMetric.MetricGeometry.curveLength γ a b :=
      LQGMetric.MetricGeometry.curveLength_mono γ htO.1 htP.2
    _ ≤ edist (D.pt x) (D.pt y) + ENNReal.ofReal ε := hlen
    _ = ENNReal.ofReal (D.1 (x, y)) + ε := by
      rw [LQGMetric.ContMetric.edist_pt, ENNReal.ofReal_coe_nnreal]

end SupercriticalLQGUniqueness.B2.DG20Lim
