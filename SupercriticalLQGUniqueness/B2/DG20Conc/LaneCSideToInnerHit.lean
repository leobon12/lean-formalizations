import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoSideCarrier
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorHit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set LQGMetric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_separator_hits_prefix_of_side_path
    {X E F S : Set ℂ} (hsep : LQGMetric.Disconnects X E F)
    (hno : (X ∩ S) = ∅)
    {y : ℂ} {γ : ℝ → ℂ} {m : ℝ}
    (hyF : y ∈ F) (hside : Path y (γ 0))
    (hsideS : ∀ t, hside t ∈ S)
    (hm : m ∈ Icc (0 : ℝ) 1)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hmid : γ m ∈ E) :
    ∃ t ∈ Icc (0 : ℝ) m, γ t ∈ X := by
  let γpre := pathOfIcc γ hm.1
    (hγ.mono (Icc_subset_Icc le_rfl hm.2))
  have hγpre0 : γpre 0 = γ 0 := by simp [γpre]
  have hγprem : γpre 1 = γ m := by simp [γpre]
  have hsepHit := hsep.symm y (γ m) (hside.trans γpre) hyF hmid
  obtain ⟨z, hzRange, hzX⟩ := hsepHit
  rw [Path.trans_range] at hzRange
  rcases hzRange with hzSide | hzPre
  · obtain ⟨u, rfl⟩ := hzSide
    have : hside u ∈ X ∩ S := ⟨hzX, hsideS u⟩
    exact False.elim (by simpa [hno] using this)
  · obtain ⟨t, ht, htz⟩ := range_pathOfIcc_subset γ hm.1
      (hγ.mono (Icc_subset_Icc le_rfl hm.2)) hzPre
    exact ⟨t, ht, htz ▸ hzX⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
