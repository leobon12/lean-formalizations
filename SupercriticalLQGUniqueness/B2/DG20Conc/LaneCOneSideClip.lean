import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLastSideZero

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_clip_left_side_arc
    (D : ContMetric) {Fr : Set ℂ} {α : ℝ → ℂ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hFr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ Fr)
    (hleft : α 0 ∈ (rectAB 1 1).side₁)
    (hend : α 1 ∈ (rectAB 1 1).toSet)
    (him : ∀ t ∈ Icc (0 : ℝ) 1, (α t).im ∈ Icc (0 : ℝ) 1)
    (hreUpper : ∀ t ∈ Icc (0 : ℝ) 1, (α t).re ≤ 1) :
    ∃ β : ℝ → ℂ,
      ContinuousOn β (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, β t ∈ Fr ∧ β t ∈ (rectAB 1 1).toSet) ∧
      β 0 ∈ (rectAB 1 1).side₁ ∧ β 1 = α 1 ∧
      D.len β 0 1 ≤ D.len α 0 1 := by
  have hleft0 : (α 0).re = 0 := (mem_rectAB_side₁.mp hleft).1
  have hend0 : 0 ≤ (α 1).re := (mem_rectAB_toSet.mp hend).1.1
  obtain ⟨c, hc, hcz, hafter⟩ :=
    laneC_exists_last_zero_nonneg zero_le_one
      (Complex.continuous_re.comp_continuousOn hα) hleft0 hend0
  let β := SupercriticalLQGUniqueness.B2.Strong.seg α c 1
  have hβ : ContinuousOn β (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hα hc ⟨zero_le_one, le_rfl⟩
  have hβ0 : β 0 = α c := by simp [β]
  have hβ1 : β 1 = α 1 := by
    dsimp [β, SupercriticalLQGUniqueness.B2.Strong.seg]
    congr 1
    ring
  refine ⟨β, hβ, ?_, ?_, hβ1, ?_⟩
  · intro t ht
    have hp := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem
      hc (show (1 : ℝ) ∈ Icc 0 1 by simp) ht
    have hp' : c ≤ c + t * (1 - c) := by
      have htc : 0 ≤ t := ht.1
      have hc1 : 0 ≤ 1 - c := sub_nonneg.mpr hc.2
      nlinarith [mul_nonneg hc1 htc]
    have hnonneg : 0 ≤ (β t).re := by
      simpa [β, SupercriticalLQGUniqueness.B2.Strong.seg] using
        hafter (c + t * (1 - c)) ⟨hp', hp.2⟩
    constructor
    · exact hFr _ hp
    · apply mem_rectAB_toSet.mpr
      constructor
      · exact ⟨hnonneg, hreUpper _ hp⟩
      · exact him _ hp
  · rw [hβ0, mem_rectAB_side₁]
    exact ⟨hcz, him c hc⟩
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ α) hc (show (1 : ℝ) ∈ Icc 0 1 by simp)

 

theorem laneC_clip_right_side_arc
    (D : ContMetric) {Fr : Set ℂ} {α : ℝ → ℂ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hFr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ Fr)
    (hstart : α 0 ∈ (rectAB 1 1).toSet)
    (hright : α 1 ∈ (rectAB 1 1).side₂)
    (him : ∀ t ∈ Icc (0 : ℝ) 1, (α t).im ∈ Icc (0 : ℝ) 1)
    (hreLower : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (α t).re) :
    ∃ β : ℝ → ℂ,
      ContinuousOn β (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, β t ∈ Fr ∧ β t ∈ (rectAB 1 1).toSet) ∧
      β 0 = α 0 ∧ β 1 ∈ (rectAB 1 1).side₂ ∧
      D.len β 0 1 ≤ D.len α 0 1 := by
  have hright1 : (α 1).re = 1 := (mem_rectAB_side₂.mp hright).1
  have hstart1 : (α 0).re ≤ 1 := (mem_rectAB_toSet.mp hstart).1.2
  obtain ⟨c, hc, hcz, hbefore⟩ :=
    laneC_exists_first_zero_nonneg zero_le_one
      ((continuousOn_const.sub (Complex.continuous_re.comp_continuousOn hα)))
      (by change 0 ≤ 1 - (α 0).re; linarith)
      (by change 1 - (α 1).re = 0; linarith)
  let β := SupercriticalLQGUniqueness.B2.Strong.seg α 0 c
  have hβ : ContinuousOn β (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hα
      (show (0 : ℝ) ∈ Icc 0 1 by simp) hc
  have hβ0 : β 0 = α 0 := by simp [β]
  have hβ1 : β 1 = α c := by
    dsimp [β, SupercriticalLQGUniqueness.B2.Strong.seg]
    congr 1
    ring
  refine ⟨β, hβ, ?_, hβ0, ?_, ?_⟩
  · intro t ht
    have hp := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem
      (show (0 : ℝ) ∈ Icc 0 1 by simp) hc ht
    have hp' : t * c ∈ Icc (0 : ℝ) c := by
      have hc0 : 0 ≤ c := hc.1
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      constructor
      · exact mul_nonneg ht0 hc0
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hc0]
    have hupper : (β t).re ≤ 1 := by
      have h := hbefore (t * c) hp'
      change 0 ≤ 1 - (α (t * c)).re at h
      have h' : 0 ≤ 1 - (β t).re := by
        simpa [β, SupercriticalLQGUniqueness.B2.Strong.seg] using h
      nlinarith
    constructor
    · exact hFr _ hp
    · apply mem_rectAB_toSet.mpr
      constructor
      · exact ⟨hreLower _ hp, hupper⟩
      · exact him _ hp
  · rw [hβ1, mem_rectAB_side₂]
    constructor
    · change 1 - (α c).re = 0 at hcz
      linarith
    · exact him c hc
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ α) (show (0 : ℝ) ∈ Icc 0 1 by simp) hc

end SupercriticalLQGUniqueness.B2.DG20Conc
