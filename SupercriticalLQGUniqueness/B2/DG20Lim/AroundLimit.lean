import SupercriticalLQGUniqueness.B2.DG20Lim.LSCConvergence

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

def RatAnnulus.OppositePoints (A : RatAnnulus) (z z' : ℂ) : Prop :=
  (z ∈ A.inner.openDisk ∧ z' ∉ A.outer.closedDisk) ∨
    (z' ∈ A.inner.openDisk ∧ z ∉ A.outer.closedDisk)

theorem RatAnnulus.oppositePoints_ne (A : RatAnnulus) {z z' : ℂ}
    (h : A.OppositePoints z z') : z ≠ z' := by
  intro heq
  rcases h with ⟨hz, hz'⟩ | ⟨hz', hz⟩
  · exact hz' (heq ▸ A.outer.openDisk_subset_closedDisk
      (A.nested.2 (A.inner.openDisk_subset_closedDisk hz)))
  · exact hz (heq.symm ▸ A.outer.openDisk_subset_closedDisk
      (A.nested.2 (A.inner.openDisk_subset_closedDisk hz')))

theorem RatAnnulus.eventually_oppositeSides (A : RatAnnulus) {z z' : ℂ}
    (h : A.OppositePoints z z') (O P : ℕ → RatCircle)
    (hO : ∀ᶠ n in atTop, (O n).Surrounds z)
    (hP : ∀ᶠ n in atTop, (P n).Surrounds z')
    (hrO : Tendsto (fun n => ((O n).radius : ℝ)) atTop (nhds 0))
    (hrP : Tendsto (fun n => ((P n).radius : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, A.OppositeSides (O n) (P n) := by
  rcases h with ⟨hz, hz'⟩ | ⟨hz', hz⟩
  · have heO := RatCircle.eventually_nested ⟨A.inner_pos, hz⟩ O hO hrO
    have heP := RatCircle.eventually_outside hz' P hP hrP
    filter_upwards [heO, heP] with n hnO hnP
    left
    constructor
    · exact (O n).toSet_subset_closedDisk.trans
        (hnO.2.trans A.inner.openDisk_subset_closedDisk)
    · intro u hu huA
      exact hnP ((P n).toSet_subset_closedDisk hu)
        (A.outer.openDisk_subset_closedDisk huA)
  · have heO := RatCircle.eventually_outside hz O hO hrO
    have heP := RatCircle.eventually_nested ⟨A.inner_pos, hz'⟩ P hP hrP
    filter_upwards [heO, heP] with n hnO hnP
    right
    constructor
    · exact (P n).toSet_subset_closedDisk.trans
        (hnP.2.trans A.inner.openDisk_subset_closedDisk)
    · intro u hu huA
      exact hnO ((O n).toSet_subset_closedDisk hu)
        (A.outer.openDisk_subset_closedDisk huA)

 

theorem RData.DfromR_le_add_around (R : RData) (A : RatAnnulus)
    (z w z' w' : ℂ) (hz : A.OppositePoints z z')
    (hw : A.OppositePoints w w') :
    R.DfromR z w ≤ R.DfromR z z' + R.DfromR w w' + R.around A := by
  by_cases hzw : z = w
  · subst w
    simp only [R.DfromR_self]
    exact zero_le
  have hzz' := A.oppositePoints_ne hz
  have hww' := A.oppositePoints_ne hw
  obtain ⟨Oz, hOz, hrOz⟩ := exists_shrinking_ratCircles z
  obtain ⟨Ow, hOw, hrOw⟩ := exists_shrinking_ratCircles w
  obtain ⟨Oz', hOz', hrOz'⟩ := exists_shrinking_ratCircles z'
  obtain ⟨Ow', hOw', hrOw'⟩ := exists_shrinking_ratCircles w'
  have hL := R.tendsto_across_shrinking hzw Oz Ow
    (Eventually.of_forall fun n => (hOz n).1)
    (Eventually.of_forall fun n => (hOw n).1) hrOz hrOw
  have hR1 := R.tendsto_across_shrinking hzz' Oz Oz'
    (Eventually.of_forall fun n => (hOz n).1)
    (Eventually.of_forall fun n => (hOz' n).1) hrOz hrOz'
  have hR2 := R.tendsto_across_shrinking hww' Ow Ow'
    (Eventually.of_forall fun n => (hOw n).1)
    (Eventually.of_forall fun n => (hOw' n).1) hrOw hrOw'
  have he1 := A.eventually_oppositeSides hz Oz Oz'
    (Eventually.of_forall fun n => (hOz n).1)
    (Eventually.of_forall fun n => (hOz' n).1) hrOz hrOz'
  have he2 := A.eventually_oppositeSides hw Ow Ow'
    (Eventually.of_forall fun n => (hOw n).1)
    (Eventually.of_forall fun n => (hOw' n).1) hrOw hrOw'
  have hineq : ∀ᶠ n in atTop,
      R.across (Oz n) (Ow n) ≤
        R.across (Oz n) (Oz' n) + R.across (Ow n) (Ow' n) + R.around A := by
    filter_upwards [he1, he2] with n hn1 hn2
    exact R.around_upper A (Oz n) (Oz' n) (Ow n) (Ow' n) hn1 hn2
  have hconst : Tendsto (fun _ : ℕ => R.around A) atTop (nhds (R.around A)) :=
    tendsto_const_nhds
  have hrhs : Tendsto
      (fun n => R.across (Oz n) (Oz' n) + R.across (Ow n) (Ow' n) + R.around A)
      atTop (nhds (R.DfromR z z' + R.DfromR w w' + R.around A)) :=
    (hR1.add hR2).add hconst
  exact le_of_tendsto_of_tendsto hL hrhs hineq

end SupercriticalLQGUniqueness.B2.DG20Lim
