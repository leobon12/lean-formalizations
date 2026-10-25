import SupercriticalLQGUniqueness.B2.DG20Lim.ChainOne

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.across_le_DfromR_of_nested_sides
    (R : RData) (O P : RatCircle) (u v : ℂ)
    (hOP : P.SurroundsCircle O)
    (hu : u ∈ O.openDisk) (hv : v ∈ P.closedDiskᶜ) :
    R.across O P ≤ R.DfromR u v := by
  have hdisj : Disjoint O.toSet P.toSet := RatCircle.disjoint_of_nested hOP
  have hOPout : P.toSet ⊆ O.openDiskᶜ := by
    intro x hxP hxO
    have hxP' : x ∈ P.closedDisk := P.toSet_subset_closedDisk hxP
    have hxO' : x ∈ P.openDisk := hOP.2
      (O.openDisk_subset_closedDisk hxO)
    exact (ne_of_lt (mem_ball.mp hxO')) (mem_sphere.mp hxP)
  have hPOin : O.toSet ⊆ P.openDisk :=
    O.toSet_subset_closedDisk.trans hOP.2
  have huO : u ∉ O.toSet := by
    intro hu'
    exact (ne_of_lt (mem_ball.mp hu)) (mem_sphere.mp hu')
  have hvP : v ∉ P.toSet := by
    intro hv'
    exact hv (P.toSet_subset_closedDisk hv')
  have hsepU : O.DisconnectsPoint u P :=
    ⟨huO, O.disconnects_of_subsets (by simpa using hu) hOPout⟩
  have hsepV : P.DisconnectsPoint v O :=
    ⟨hvP, disconnects_symm (P.disconnects_of_subsets hPOin (by
      intro x hx hvx
      have hxv : x = v := by simpa only [mem_singleton_iff] using hx
      subst x
      exact hv (P.openDisk_subset_closedDisk hvx)))⟩
  have huv : u ≠ v := by
    intro heq
    subst v
    exact hv (P.openDisk_subset_closedDisk (hOP.2 (O.openDisk_subset_closedDisk hu)))
  exact R.across_le_DfromR_of_two_circle_chain O P u v huv hdisj hsepU hsepV

end SupercriticalLQGUniqueness.B2.DG20Lim
