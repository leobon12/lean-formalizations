import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSoutheastSector
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLastSideZero
import SupercriticalLQGUniqueness.B2.Strong.Glue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 


theorem laneC_corner_crosscut_of_sweep
    (D : ContMetric) {ρ : ℝ → ℂ} {a b s u t : ℝ}
    (hs : s ∈ Icc a b) (hu : u ∈ Icc a b)
    (ht : t ∈ Icc a b) (hsu : s ≤ u) (hut : u ≤ t)
    (hρ : ContinuousOn ρ (Icc a b))
    {c : ℂ} {r : ℝ}
    (hρann : ∀ x ∈ Icc a b,
      r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r)
    (hwest : (ρ s).re < 0) (hnorth : 1 < (ρ t).im)
    (hanchorRe : 0 ≤ (ρ u).re) (hanchorIm : (ρ u).im ≤ 1)
    (hpre : ∀ x ∈ Icc s u, (ρ x).im ≤ 1)
    (hpost : ∀ x ∈ Icc u t, 0 ≤ (ρ x).re)
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
  have hρtop : ContinuousOn (fun x => 1 - (ρ x).im) (Icc a b) :=
    continuousOn_const.sub (Complex.continuous_im.comp_continuousOn hρ)
  have hsuSub : Icc s u ⊆ Icc a b := Icc_subset_Icc hs.1 hu.2
  have hutSub : Icc u t ⊆ Icc a b := Icc_subset_Icc hu.1 ht.2
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ Icc s u, (ρ q).re = 0 :=
    intermediate_value_Icc hsu (hρre.mono hsuSub)
      ⟨hwest.le, hanchorRe⟩
  obtain ⟨l, hl, hl0, hlpos⟩ :=
    laneC_exists_last_zero_nonneg hq.2
      (hρre.mono (Icc_subset_Icc (hs.1.trans hq.1) hu.2)) hq0 hanchorRe
  obtain ⟨q', hq', hq'0⟩ : ∃ q' ∈ Icc u t, 1 - (ρ q').im = 0 :=
    intermediate_value_Icc' hut (hρtop.mono hutSub)
      ⟨by linarith, by linarith⟩
  obtain ⟨v, hv, hv0, hvpos⟩ :=
    laneC_exists_first_zero_nonneg hq'.1
      (hρtop.mono (Icc_subset_Icc hu.1 (hq'.2.trans ht.2)))
      (by linarith : 0 ≤ 1 - (ρ u).im) hq'0
  have hlmem : l ∈ Icc a b := ⟨hs.1.trans (hq.1.trans hl.1), hl.2.trans hu.2⟩
  have hvmem : v ∈ Icc a b := ⟨hu.1.trans hv.1, hv.2.trans (hq'.2.trans ht.2)⟩
  have hlv : l ≤ v := hl.2.trans hv.1
  let α := SupercriticalLQGUniqueness.B2.Strong.seg ρ l v
  have hα : ContinuousOn α (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ hlmem hvmem
  have hsegmem (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      l + w * (v - l) ∈ Icc l v := by
    constructor <;> nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hlv),
      mul_le_mul_of_nonneg_right hw.2 (sub_nonneg.mpr hlv)]
  have hαcar (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      α w ∈ (rectAB 1 1).toSet := by
    let x := l + w * (v - l)
    have hx : x ∈ Icc l v := hsegmem w hw
    have hxst : x ∈ Icc s t :=
      ⟨(hq.1.trans hl.1).trans hx.1, hx.2.trans (hv.2.trans hq'.2)⟩
    have hxo := hother x hxst
    have hxre : 0 ≤ (ρ x).re := by
      by_cases hxu : x ≤ u
      · exact hlpos x ⟨hx.1, hxu⟩
      · exact hpost x ⟨le_of_not_ge hxu, hx.2.trans (hv.2.trans hq'.2)⟩
    have hxim : (ρ x).im ≤ 1 := by
      by_cases hxu : x ≤ u
      · exact hpre x ⟨(hq.1.trans hl.1).trans hx.1, hxu⟩
      · have h := hvpos x ⟨le_of_not_ge hxu, hx.2⟩
        linarith
    have hsq : ρ x ∈ (rectAB 1 1).toSet := by
      rw [mem_rectAB_toSet]
      exact ⟨⟨hxre, hxo.2⟩, ⟨hxo.1, hxim⟩⟩
    simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg, x] using hsq
  refine ⟨α, hα, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hx := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hlmem hvmem hw
    exact ⟨(hρann _ hx).1, (hρann _ hx).2, hαcar w hw⟩
  · have hleft : ρ l ∈ (rectAB 1 1).side₁ := by
      rw [mem_rectAB_side₁]
      have hlother := hother l
        ⟨(hq.1.trans hl.1), hl.2.trans hut⟩
      exact ⟨hl0, hlother.1, (hpre l ⟨hq.1.trans hl.1, hl.2⟩)⟩
    simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg] using hleft
  · have htop : (ρ v).im = 1 := by linarith
    simpa [α, SupercriticalLQGUniqueness.B2.Strong.seg] using htop
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ ρ) hlmem hvmem

end SupercriticalLQGUniqueness.B2.DG20Conc
