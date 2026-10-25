import SupercriticalLQGUniqueness.B2.DG20Lim.DfromR
import Mathlib.Topology.Order.IntermediateValue

 

set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem sphere_disconnects_of_subsets (c : ℂ) (r : ℝ) {E F : Set ℂ}
    (hE : E ⊆ ball c r) (hF : F ⊆ (ball c r)ᶜ) :
    Disconnects (sphere c r) E F := by
  intro h
  obtain ⟨S, hS, hcomp, hSE, hSF⟩ := h
  obtain ⟨x, hxS, hxE⟩ := hSE
  obtain ⟨y, hyS, hyF⟩ := hSF
  have hxy : r ∈ Set.Icc (dist x c) (dist y c) := by
    constructor
    · exact (mem_ball.mp (hE hxE)).le
    · exact le_of_not_gt (hF hyF)
  obtain ⟨p, hpS, hpR⟩ := hS.intermediate_value hxS hyS
    ((continuous_id.dist continuous_const).continuousOn) hxy
  exact (hcomp hpS) (mem_sphere.mpr hpR)

theorem RatCircle.disconnects_of_subsets (O : RatCircle) {E F : Set ℂ}
    (hE : E ⊆ O.openDisk) (hF : F ⊆ O.openDiskᶜ) :
    Disconnects O.toSet E F :=
  sphere_disconnects_of_subsets O.center (O.radius : ℝ) hE hF

theorem disconnects_symm {K E F : Set ℂ} (h : Disconnects K E F) :
    Disconnects K F E := by
  intro h'
  apply h
  obtain ⟨S, hS, hSK, hSF, hSE⟩ := h'
  exact ⟨S, hS, hSK, hSE, hSF⟩

theorem RatCircle.toSet_subset_closedDisk (O : RatCircle) :
    O.toSet ⊆ O.closedDisk :=
  sphere_subset_closedBall

theorem RatCircle.openDisk_subset_closedDisk (O : RatCircle) :
    O.openDisk ⊆ O.closedDisk :=
  ball_subset_closedBall

theorem RatCircle.disjoint_of_nested {O I : RatCircle}
    (h : O.SurroundsCircle I) : Disjoint I.toSet O.toSet := by
  apply disjoint_left.mpr
  intro z hzI hzO
  have hzin : z ∈ O.openDisk := h.2 (I.toSet_subset_closedDisk hzI)
  exact (ne_of_lt (mem_ball.mp hzin)) (mem_sphere.mp hzO)

theorem RatCircle.toSet_subset_of_nested {O I : RatCircle}
    (h : O.SurroundsCircle I) : I.toSet ⊆ O.closedDisk :=
  I.toSet_subset_closedDisk.trans (h.2.trans O.openDisk_subset_closedDisk)

 

theorem RData.across_outer_le_inner_of_nested (R : RData) (a b c d : RatCircle)
    (hab : b.SurroundsCircle a) (hcd : c.SurroundsCircle d)
    (hbc : Disjoint b.closedDisk c.closedDisk) :
    R.across b c ≤ R.across a d := by
  have hab' : Disjoint a.toSet b.toSet := RatCircle.disjoint_of_nested hab
  have hcd' : Disjoint c.toSet d.toSet := (RatCircle.disjoint_of_nested hcd).symm
  have hac : Disjoint a.toSet c.toSet :=
    hbc.mono (RatCircle.toSet_subset_of_nested hab) c.toSet_subset_closedDisk
  have had : Disjoint a.toSet d.toSet :=
    hbc.mono (RatCircle.toSet_subset_of_nested hab)
      (RatCircle.toSet_subset_of_nested hcd)
  have hbc' : Disjoint b.toSet c.toSet :=
    hbc.mono b.toSet_subset_closedDisk c.toSet_subset_closedDisk
  have hbd : Disjoint b.toSet d.toSet :=
    hbc.mono b.toSet_subset_closedDisk (RatCircle.toSet_subset_of_nested hcd)
  have hsepB : Disconnects b.toSet a.toSet c.toSet := by
    apply b.disconnects_of_subsets
    · exact a.toSet_subset_closedDisk.trans hab.2
    · intro z hzC hzIn
      exact (Set.disjoint_left.mp hbc) (b.openDisk_subset_closedDisk hzIn)
        (c.toSet_subset_closedDisk hzC)
  have hsepC : Disconnects c.toSet b.toSet d.toSet := by
    apply disconnects_symm
    apply c.disconnects_of_subsets
    · exact d.toSet_subset_closedDisk.trans hcd.2
    · intro z hzB hzIn
      exact (Set.disjoint_left.mp hbc) (b.toSet_subset_closedDisk hzB)
        (c.openDisk_subset_closedDisk hzIn)
  apply R.across_outer_le_inner a b c d ?_ hsepB hsepC
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm]

 

theorem RatCircle.nested_of_small_radius {A I : RatCircle} {z : ℂ}
    (hA : A.Surrounds z) (hI : I.Surrounds z)
    (hsmall : 2 * (I.radius : ℝ) < (A.radius : ℝ) - dist z A.center) :
    A.SurroundsCircle I := by
  refine ⟨hA.1, ?_⟩
  intro u hu
  have h₁ : dist u I.center ≤ (I.radius : ℝ) := mem_closedBall.mp hu
  have h₂ : dist I.center z < (I.radius : ℝ) := by
    simpa only [dist_comm] using (mem_ball.mp hI.2)
  have h₃ : dist u A.center ≤ dist u I.center + dist I.center z + dist z A.center := by
    calc
      dist u A.center ≤ dist u I.center + dist I.center A.center := dist_triangle _ _ _
      _ ≤ dist u I.center + (dist I.center z + dist z A.center) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  show u ∈ A.openDisk
  apply mem_ball.mpr
  linarith

 

theorem RatCircle.eventually_nested {A : RatCircle} {z : ℂ} (hA : A.Surrounds z)
    (I : ℕ → RatCircle)
    (hI : ∀ᶠ n in Filter.atTop, (I n).Surrounds z)
    (hrad : Filter.Tendsto (fun n => ((I n).radius : ℝ)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, A.SurroundsCircle (I n) := by
  have hmargin : 0 < ((A.radius : ℝ) - dist z A.center) :=
    sub_pos.mpr (mem_ball.mp hA.2)
  have hev := (tendsto_order.1 hrad).2
    (((A.radius : ℝ) - dist z A.center) / 2) (half_pos hmargin)
  filter_upwards [hI, hev] with n hn hsmall
  apply RatCircle.nested_of_small_radius hA hn
  linarith

 

theorem RatCircle.eventually_outside {A : RatCircle} {z : ℂ}
    (hz : z ∉ A.closedDisk) (I : ℕ → RatCircle)
    (hI : ∀ᶠ n in Filter.atTop, (I n).Surrounds z)
    (hrad : Filter.Tendsto (fun n => ((I n).radius : ℝ)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, (I n).closedDisk ⊆ A.closedDiskᶜ := by
  have hout : (A.radius : ℝ) < dist z A.center := by
    simpa only [RatCircle.closedDisk, mem_closedBall, not_le] using hz
  have hmargin : 0 < dist z A.center - (A.radius : ℝ) := sub_pos.mpr hout
  have hev := (tendsto_order.1 hrad).2
    ((dist z A.center - (A.radius : ℝ)) / 2) (half_pos hmargin)
  filter_upwards [hI, hev] with n hn hsmall
  intro u hu
  have h₁ : dist u (I n).center ≤ ((I n).radius : ℝ) := mem_closedBall.mp hu
  have h₂ : dist (I n).center z < ((I n).radius : ℝ) := by
    simpa only [dist_comm] using (mem_ball.mp hn.2)
  have htri : dist z A.center ≤ dist z u + dist u A.center := dist_triangle _ _ _
  have hzu : dist z u ≤ dist u (I n).center + dist (I n).center z := by
    simpa only [dist_comm] using (dist_triangle u (I n).center z)
  show u ∈ A.closedDiskᶜ
  simp only [RatCircle.closedDisk, mem_compl_iff, mem_closedBall, not_le]
  linarith

 

theorem eventually_disjoint_shrinking_disks {z w : ℂ} (hzw : z ≠ w)
    (O P : ℕ → RatCircle)
    (hO : ∀ᶠ n in Filter.atTop, (O n).Surrounds z)
    (hP : ∀ᶠ n in Filter.atTop, (P n).Surrounds w)
    (hrO : Filter.Tendsto (fun n => ((O n).radius : ℝ)) Filter.atTop (nhds 0))
    (hrP : Filter.Tendsto (fun n => ((P n).radius : ℝ)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, Disjoint (O n).closedDisk (P n).closedDisk := by
  have hdist : 0 < dist z w := dist_pos.mpr hzw
  have heO := (tendsto_order.1 hrO).2 (dist z w / 4) (by positivity)
  have heP := (tendsto_order.1 hrP).2 (dist z w / 4) (by positivity)
  filter_upwards [hO, hP, heO, heP] with n hnO hnP hsO hsP
  apply closedBall_disjoint_closedBall
  have hcz : dist z (O n).center < ((O n).radius : ℝ) :=
    mem_ball.mp hnO.2
  have hcw : dist (P n).center w < ((P n).radius : ℝ) := by
    simpa only [dist_comm] using (mem_ball.mp hnP.2)
  have htri : dist z w ≤ dist z (O n).center +
      dist (O n).center (P n).center + dist (P n).center w := by
    calc
      dist z w ≤ dist z (O n).center + dist (O n).center w := dist_triangle _ _ _
      _ ≤ dist z (O n).center +
          (dist (O n).center (P n).center + dist (P n).center w) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  linarith

 

theorem RData.tendsto_across_shrinking (R : RData) {z w : ℂ} (hzw : z ≠ w)
    (O P : ℕ → RatCircle)
    (hO : ∀ᶠ n in Filter.atTop, (O n).Surrounds z)
    (hP : ∀ᶠ n in Filter.atTop, (P n).Surrounds w)
    (hrO : Filter.Tendsto (fun n => ((O n).radius : ℝ)) Filter.atTop (nhds 0))
    (hrP : Filter.Tendsto (fun n => ((P n).radius : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => R.across (O n) (P n)) Filter.atTop
      (nhds (R.DfromR z w)) := by
  have hdisj := eventually_disjoint_shrinking_disks hzw O P hO hP hrO hrP
  apply R.tendsto_DfromR_of_cofinal hzw O P ?_ ?_
  · filter_upwards [hO, hP, hdisj] with n hnO hnP hnD
    exact ⟨hnO, hnP, hnD⟩
  · intro A B hA hB hAB
    have heA := RatCircle.eventually_nested hA O hO hrO
    have heB := RatCircle.eventually_nested hB P hP hrP
    filter_upwards [heA, heB] with n hnA hnB
    exact R.across_outer_le_inner_of_nested (O n) A B (P n) hnA hnB hAB

end SupercriticalLQGUniqueness.B2.DG20Lim
