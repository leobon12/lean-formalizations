import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoSideCarrier

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_trace_square_of_no_right_side
    {ρ : ℝ → ℂ} {a b : ℝ} (_hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hstrip : ∀ s ∈ Icc a b, (ρ s).im ∈ Icc (0 : ℝ) 1)
    (hlower : ∀ s ∈ Icc a b, 0 ≤ (ρ s).re)
    (hhit : ((ρ '' Icc a b) ∩ (rectAB 1 1).toSet).Nonempty)
    (hno : ¬((ρ '' Icc a b) ∩ (rectAB 1 1).side₂).Nonempty) :
    ∀ s ∈ Icc a b, ρ s ∈ (rectAB 1 1).toSet := by
  obtain ⟨_, ⟨s₀, hs₀, hs₀eq⟩, hs₀sq⟩ := hhit
  have hs₀re : (ρ s₀).re ≤ 1 :=
    (mem_rectAB_toSet.mp (hs₀eq ▸ hs₀sq)).1.2
  have hcont : ContinuousOn (fun t => 1 - (ρ t).re) (Icc a b) :=
    continuousOn_const.sub (Complex.continuous_re.comp_continuousOn hρ)
  intro s hs
  have hsre : (ρ s).re ≤ 1 := by
    by_contra hgt
    have hlt : 1 - (ρ s).re ≤ 0 := by linarith
    have hs₀pos : 0 ≤ 1 - (ρ s₀).re := by linarith
    by_cases hss : s ≤ s₀
    · obtain ⟨u, hu, hzero⟩ : ∃ u ∈ Icc s s₀, 1 - (ρ u).re = 0 :=
        intermediate_value_Icc hss
          (hcont.mono (Icc_subset_Icc hs.1 hs₀.2))
          ⟨hlt, hs₀pos⟩
      apply hno
      have huab : u ∈ Icc a b :=
        ⟨hs.1.trans hu.1, hu.2.trans hs₀.2⟩
      exact ⟨ρ u, ⟨u, huab, rfl⟩,
        mem_rectAB_side₂.mpr ⟨(by linarith), hstrip u huab⟩⟩
    · have hs₀s : s₀ ≤ s := le_of_not_ge hss
      obtain ⟨u, hu, hzero⟩ : ∃ u ∈ Icc s₀ s, 1 - (ρ u).re = 0 :=
        intermediate_value_Icc' hs₀s
          (hcont.mono (Icc_subset_Icc hs₀.1 hs.2))
          ⟨hlt, hs₀pos⟩
      apply hno
      have huab : u ∈ Icc a b :=
        ⟨hs₀.1.trans hu.1, hu.2.trans hs.2⟩
      exact ⟨ρ u, ⟨u, huab, rfl⟩,
        mem_rectAB_side₂.mpr ⟨(by linarith), hstrip u huab⟩⟩
  exact mem_rectAB_toSet.mpr ⟨⟨hlower s hs, hsre⟩, hstrip s hs⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
