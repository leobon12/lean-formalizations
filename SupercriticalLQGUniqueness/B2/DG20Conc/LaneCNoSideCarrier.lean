import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOneSideAnnulus
import Mathlib.Topology.Order.IntermediateValue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_trace_square_of_no_left_side
    {ρ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hstrip : ∀ s ∈ Icc a b, (ρ s).im ∈ Icc (0 : ℝ) 1)
    (hupper : ∀ s ∈ Icc a b, (ρ s).re ≤ 1)
    (hhit : ((ρ '' Icc a b) ∩ (rectAB 1 1).toSet).Nonempty)
    (hno : ¬((ρ '' Icc a b) ∩ (rectAB 1 1).side₁).Nonempty) :
    ∀ s ∈ Icc a b, ρ s ∈ (rectAB 1 1).toSet := by
  obtain ⟨_, ⟨s₀, hs₀, hs₀eq⟩, hs₀sq⟩ := hhit
  have hs₀re : 0 ≤ (ρ s₀).re := by
    exact (mem_rectAB_toSet.mp (hs₀eq ▸ hs₀sq)).1.1
  have hcont : ContinuousOn (fun t => (ρ t).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn hρ
  intro s hs
  have hsre : 0 ≤ (ρ s).re := by
    by_contra hneg
    have hlt : (ρ s).re ≤ 0 := le_of_not_ge hneg
    by_cases hss : s ≤ s₀
    · obtain ⟨u, hu, hzero⟩ : ∃ u ∈ Icc s s₀, (ρ u).re = 0 :=
        intermediate_value_Icc hss
          (hcont.mono (Icc_subset_Icc hs.1 hs₀.2))
          ⟨hlt, hs₀re⟩
      apply hno
      exact ⟨ρ u, ⟨u, ⟨hs.1.trans hu.1, hu.2.trans hs₀.2⟩, rfl⟩,
        mem_rectAB_side₁.mpr ⟨hzero, hstrip u
          ⟨hs.1.trans hu.1, hu.2.trans hs₀.2⟩⟩⟩
    · have hs₀s : s₀ ≤ s := le_of_not_ge hss
      obtain ⟨u, hu, hzero⟩ : ∃ u ∈ Icc s₀ s, (ρ u).re = 0 :=
        intermediate_value_Icc' hs₀s
          (hcont.mono (Icc_subset_Icc hs₀.1 hs.2))
          ⟨hlt, hs₀re⟩
      apply hno
      exact ⟨ρ u, ⟨u, ⟨hs₀.1.trans hu.1, hu.2.trans hs.2⟩, rfl⟩,
        mem_rectAB_side₁.mpr ⟨hzero, hstrip u
          ⟨hs₀.1.trans hu.1, hu.2.trans hs.2⟩⟩⟩
  exact mem_rectAB_toSet.mpr ⟨⟨hsre, hupper s hs⟩, hstrip s hs⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
