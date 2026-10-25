import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerCrosscutCriterion

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_corner_crosscut_of_first_top
    (D : ContMetric) {ρ : ℝ → ℂ} {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hρ : ContinuousOn ρ (Icc a b))
    {c : ℂ} {r : ℝ}
    (hρann : ∀ x ∈ Icc a b,
      r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r)
    (hwest : (ρ s).re < 0) (htop : (ρ t).im = 1)
    (htopRe : 0 ≤ (ρ t).re)
    (hpre : ∀ x ∈ Icc s t, (ρ x).im ≤ 1)
    (hother : ∀ x ∈ Icc s t, 0 ≤ (ρ x).im ∧ (ρ x).re ≤ 1) :
    ∃ α : ℝ → ℂ,
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ v ∈ Icc (0 : ℝ) 1,
        r < dist (α v) c ∧ dist (α v) c < 2 * r ∧
          α v ∈ (rectAB 1 1).toSet) ∧
      α 0 ∈ (rectAB 1 1).side₁ ∧
      (α 1).im = 1 ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  have hρre : ContinuousOn (fun x => (ρ x).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn hρ
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Icc s t, (ρ q).re = 0 :=
    intermediate_value_Icc hst
      (hρre.mono (Icc_subset_Icc hs.1 ht.2))
      ⟨hwest.le, htopRe⟩
  obtain ⟨l, hl, hl0, hlpos⟩ :=
    laneC_exists_last_zero_nonneg hq.2
      (hρre.mono (Icc_subset_Icc (hs.1.trans hq.1) ht.2))
      hq0 htopRe
  have hlmem : l ∈ Icc a b := ⟨hs.1.trans (hq.1.trans hl.1), hl.2.trans ht.2⟩
  let α := SupercriticalLQGUniqueness.B2.Strong.seg ρ l t
  have hα : ContinuousOn α (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ hlmem ht
  have hcar (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      α w ∈ (rectAB 1 1).toSet := by
    let x := l + w * (t - l)
    have hx : x ∈ Icc l t := by
      constructor <;> nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hl.2),
        mul_le_mul_of_nonneg_right hw.2 (sub_nonneg.mpr hl.2)]
    have hxst : x ∈ Icc s t := ⟨(hq.1.trans hl.1).trans hx.1, hx.2⟩
    have hxo := hother x hxst
    have hsq : ρ x ∈ (rectAB 1 1).toSet := by
      rw [mem_rectAB_toSet]
      exact ⟨⟨hlpos x hx, hxo.2⟩, ⟨hxo.1, hpre x hxst⟩⟩
    simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg, x] using hsq
  refine ⟨α, hα, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hx := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hlmem ht hw
    exact ⟨(hρann _ hx).1, (hρann _ hx).2, hcar w hw⟩
  · have hleft : ρ l ∈ (rectAB 1 1).side₁ := by
      rw [mem_rectAB_side₁]
      have hlo := hother l ⟨hq.1.trans hl.1, hl.2⟩
      exact ⟨hl0, hlo.1, hpre l ⟨hq.1.trans hl.1, hl.2⟩⟩
    simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg] using hleft
  · simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg] using htop
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ ρ) hlmem ht

end SupercriticalLQGUniqueness.B2.DG20Conc
