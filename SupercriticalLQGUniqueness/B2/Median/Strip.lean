import SupercriticalLQGUniqueness.B2.Median.Lower
import LQGMetric.Topo.RectCross

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness.B2.Median

theorem exists_leftRightCrossing_of_strip (ξ : ℝ) (φ : C(ℂ, ℝ))
    {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w)
    (hstrip : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (P t).im ∧ (P t).im ≤ 1)
    (hz : z.re ≤ 0) (hw : 1 ≤ w.re) :
    ∃ Q : ℝ → ℂ, IsLeftRightCrossing Q ∧ lfppLen ξ φ Q ≤ lfppLen ξ φ P := by
  have hRe : ContinuousOn (fun t => (P t).re) (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn hP.continuousOn
  obtain ⟨s, t, hs, hst, ht, hPs, hPt, hmid⟩ :=
    LQGMetric.RectCross.exists_sub_crossing (f := fun u => (P u).re)
      zero_le_one hRe (by norm_num : (0 : ℝ) ≤ 1)
      (by simpa only [hP.source] using hz)
      (by simpa only [hP.target] using hw)
  have hst' : s < t := by
    by_contra h
    have heq : s = t := le_antisymm hst (le_of_not_gt h)
    rw [heq] at hPs
    linarith
  let Q : ℝ → ℂ := LQGMetric.LFPP.subPath P s t
  have hQ : IsPiecewiseC1Path Q (P s) (P t) :=
    LQGMetric.LFPP.isPiecewiseC1Path_subPath hP hs hst' ht
  have hQ0 : Q 0 = P s := by simp [Q, LQGMetric.LFPP.subPath]
  have hQ1 : Q 1 = P t := by simp [Q, LQGMetric.LFPP.subPath]
  have hQmem : ∀ u ∈ Icc (0 : ℝ) 1, Q u ∈ unitSquare := by
    intro u hu
    have hv : (t - s) * u + s ∈ Icc s t := by
      constructor <;> nlinarith [hu.1, hu.2, sub_pos.mpr hst']
    have hreal := hmid _ hv
    have himag := hstrip _ ⟨hs.trans hv.1, hv.2.trans ht⟩
    exact ⟨hreal.1, hreal.2, himag.1, himag.2⟩
  have hQlen : lfppLen ξ φ Q ≤ lfppLen ξ φ P := by
    rw [LQGMetric.LFPP.lfppLen_subPath P hst']
    change (∫⁻ x in Icc s t, LQGMetric.LFPP.lenDens ξ φ P x) ≤
      (∫⁻ x in Icc (0 : ℝ) 1, LQGMetric.LFPP.lenDens ξ φ P x)
    exact lintegral_mono_set (Icc_subset_Icc hs ht)
  refine ⟨Q, ?_, hQlen⟩
  refine ⟨by simpa only [hQ0, hQ1] using hQ, ?_, ?_, hQmem⟩
  · rw [hQ0]
    change (P s).re = 0 ∧ 0 ≤ (P s).im ∧ (P s).im ≤ 1
    exact ⟨hPs, (hstrip s ⟨hs, hst.trans ht⟩).1,
      (hstrip s ⟨hs, hst.trans ht⟩).2⟩
  · rw [hQ1]
    change (P t).re = 1 ∧ 0 ≤ (P t).im ∧ (P t).im ≤ 1
    exact ⟨hPt, (hstrip t ⟨hs.trans hst, ht⟩).1,
      (hstrip t ⟨hs.trans hst, ht⟩).2⟩

end SupercriticalLQGUniqueness.B2.Median
