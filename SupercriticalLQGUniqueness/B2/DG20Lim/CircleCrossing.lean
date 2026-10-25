import SupercriticalLQGUniqueness.B2.DG20Lim.ApproxLower
import LQGMetric.Blueprint.M2Defs
import LQGMetric.Metric.InternalC
import LQGMetric.Metric.InternalLimitC
import Mathlib.Topology.Order.IntermediateValue

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem setDist_circles_le_pointDist (D : LQGMetric.ContMetric)
    (hD : D.IsLength) (O P : RatCircle)
    (hdisj : Disjoint O.closedDisk P.closedDisk) {x y : ℂ}
    (hx : x ∈ O.openDisk) (hy : y ∈ P.openDisk) :
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
  have hPstart : (P.radius : ℝ) < dist x P.center := by
    have hxo : x ∈ O.closedDisk := O.openDisk_subset_closedDisk hx
    have hxp : x ∉ P.closedDisk := fun hxp =>
      (Set.disjoint_left.mp hdisj) hxo hxp
    simpa only [RatCircle.closedDisk, mem_closedBall, not_le] using hxp
  have hPend : dist y P.center < (P.radius : ℝ) := mem_ball.mp hy
  have hcontP : ContinuousOn (fun t => dist (q t) P.center) (Icc a b) :=
    (continuous_id.dist continuous_const).comp_continuousOn hq
  obtain ⟨tP, htP, htPval⟩ := (isPreconnected_Icc.intermediate_value
      (right_mem_Icc.mpr hab) (left_mem_Icc.mpr hab) hcontP)
    (show (P.radius : ℝ) ∈ Icc (dist (q b) P.center) (dist (q a) P.center) by
      rw [hqa, hqb]
      exact ⟨hPend.le, hPstart.le⟩)
  have htPmem : q tP ∈ P.toSet := mem_sphere.mpr htPval
  have hOstart : dist x O.center < (O.radius : ℝ) := mem_ball.mp hx
  have hOend : (O.radius : ℝ) < dist (q tP) O.center := by
    have hpo : q tP ∉ O.closedDisk := fun hpo =>
      (Set.disjoint_left.mp hdisj) hpo (P.toSet_subset_closedDisk htPmem)
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

 


theorem RData.le_liminf_pointDist (R : RData)
    (D : ℕ → LQGMetric.ContMetric) (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (nhds (R.across O P)))
    {z w : ℂ} (zn wn : ℕ → ℂ)
    (hzn : Tendsto zn atTop (nhds z)) (hwn : Tendsto wn atTop (nhds w)) :
    R.DfromR z w ≤
      liminf (fun n => ENNReal.ofReal ((D n).1 (zn n, wn n))) atTop := by
  apply R.le_liminf_of_circle_bounds
    (fun n p => ENNReal.ofReal ((D n).1 p))
    (fun n O P => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
    hcircle z w zn wn
  intro O P hO hP hdisj
  have heO : ∀ᶠ n in atTop, zn n ∈ O.openDisk :=
    hzn (isOpen_ball.mem_nhds hO.2)
  have heP : ∀ᶠ n in atTop, wn n ∈ P.openDisk :=
    hwn (isOpen_ball.mem_nhds hP.2)
  filter_upwards [heO, heP] with n hnO hnP
  exact setDist_circles_le_pointDist (D n) (hlen n) O P hdisj hnO hnP

end SupercriticalLQGUniqueness.B2.DG20Lim
