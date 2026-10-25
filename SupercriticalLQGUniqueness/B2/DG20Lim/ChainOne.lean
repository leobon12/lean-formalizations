import SupercriticalLQGUniqueness.B2.DG20Lim.OffCircle

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatCircle.not_mem_target_of_disconnectsPoint
    {K P : RatCircle} {z : ℂ} (h : K.DisconnectsPoint z P) :
    z ∉ P.toSet := by
  intro hzP
  apply h.2
  refine ⟨{z}, isPreconnected_singleton, ?_, ?_, ?_⟩
  · intro u hu
    simpa only [mem_singleton_iff] using hu ▸ h.1
  · exact ⟨z, by simp, by simp⟩
  · exact ⟨z, by simp, hzP⟩

 

theorem RData.across_le_DfromR_of_two_circle_chain (R : RData)
    (O₀ O₁ : RatCircle) (z w : ℂ) (hzw : z ≠ w)
    (h01 : Disjoint O₀.toSet O₁.toSet)
    (hz : O₀.DisconnectsPoint z O₁)
    (hw : O₁.DisconnectsPoint w O₀) :
    R.across O₀ O₁ ≤ R.DfromR z w := by
  obtain ⟨Oz, hOz, hrOz⟩ := exists_shrinking_ratCircles z
  obtain ⟨Ow, hOw, hrOw⟩ := exists_shrinking_ratCircles w
  have hOz' : ∀ᶠ n in atTop, (Oz n).Surrounds z :=
    Eventually.of_forall fun n => (hOz n).1
  have hOw' : ∀ᶠ n in atTop, (Ow n).Surrounds w :=
    Eventually.of_forall fun n => (hOw n).1
  have hez0 := RatCircle.eventually_disjoint_fixed hz.1 Oz hOz' hrOz
  have hez1 := RatCircle.eventually_disjoint_fixed
    (RatCircle.not_mem_target_of_disconnectsPoint hz) Oz hOz' hrOz
  have hew0 := RatCircle.eventually_disjoint_fixed
    (RatCircle.not_mem_target_of_disconnectsPoint hw) Ow hOw' hrOw
  have hew1 := RatCircle.eventually_disjoint_fixed hw.1 Ow hOw' hrOw
  have hezw := eventually_disjoint_shrinking_disks hzw Oz Ow
    hOz' hOw' hrOz hrOw
  have hes0 := RatCircle.eventually_disconnects_shrinking hz Oz hOz' hrOz
  have hes1 := RatCircle.eventually_disconnects_shrinking hw Ow hOw' hrOw
  have hineq : ∀ᶠ n in atTop,
      R.across O₀ O₁ ≤ R.across (Oz n) (Ow n) := by
    filter_upwards [hez0, hez1, hew0, hew1, hezw, hes0, hes1] with
      n hnz0 hnz1 hnw0 hnw1 hnzw hns0 hns1
    have hnzw' : Disjoint (Oz n).toSet (Ow n).toSet :=
      hnzw.mono (Oz n).toSet_subset_closedDisk (Ow n).toSet_subset_closedDisk
    apply R.across_outer_le_inner (Oz n) O₀ O₁ (Ow n) ?_ hns0
      (disconnects_symm hns1)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm]
  have hlim := R.tendsto_across_shrinking hzw Oz Ow hOz' hOw' hrOz hrOw
  have hc : Tendsto (fun _ : ℕ => R.across O₀ O₁) atTop
      (nhds (R.across O₀ O₁)) := tendsto_const_nhds
  exact le_of_tendsto_of_tendsto hc hlim hineq

end SupercriticalLQGUniqueness.B2.DG20Lim
