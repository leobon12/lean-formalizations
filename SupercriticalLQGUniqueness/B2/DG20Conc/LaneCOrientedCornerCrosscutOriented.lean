import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPositiveCornerCrosscutOriented

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_oriented_corner_paid_crosscut_oriented
    (D : ContMetric) {τ : ℝ → ℂ}
    (hτ : ContinuousOn τ (Icc (0 : ℝ) 1))
    (hclosed : τ 0 = τ 1)
    {c : ℂ} {r : ℝ}
    (hτann : ∀ x ∈ Icc (0 : ℝ) 1,
      r < dist (τ x) c ∧ dist (τ x) c < 2 * r)
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim1 : c.im ≤ 1) (hTopNear : 1 - c.im ≤ r)
    (hbelow : 2 * r ≤ c.im) (hright : c.re + 2 * r ≤ 1)
    {M : ℝ → ℂ} (hM : ContinuousOn M (Icc (0 : ℝ) 1))
    (hMexp : ∀ x ∈ Icc (0 : ℝ) 1,
      Complex.exp (M x) = τ x - c)
    (hperiod : 2 * Real.pi ≤ (M 1 - M 0).im ∨
      (M 1 - M 0).im ≤ -(2 * Real.pi)) :
    ∃ α : ℝ → ℂ,
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ v ∈ Icc (0 : ℝ) 1,
        r < dist (α v) c ∧ dist (α v) c < 2 * r ∧
          α v ∈ (rectAB 1 1).toSet) ∧
      α 0 ∈ (rectAB 1 1).side₁ ∧
      (α 1).im = 1 ∧
      (α 0).im ≤ c.im ∧ c.re ≤ (α 1).re ∧
      D.len α 0 1 ≤ D.len τ 0 1 := by
  rcases hperiod with hpos | hneg
  · exact laneC_positive_corner_paid_crosscut_oriented D hτ hclosed hτann
      hcre0 hcreNear hcim1 hTopNear hbelow hright hM hMexp hpos
  · let τr := SupercriticalLQGUniqueness.B2.Strong.seg τ 1 0
    let Mr := SupercriticalLQGUniqueness.B2.Strong.seg M 1 0
    have h1 : (1 : ℝ) ∈ Icc 0 1 := by simp
    have h0 : (0 : ℝ) ∈ Icc 0 1 := by simp
    have hτr : ContinuousOn τr (Icc (0 : ℝ) 1) :=
      SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hτ h1 h0
    have hMr : ContinuousOn Mr (Icc (0 : ℝ) 1) :=
      SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hM h1 h0
    have hclosedr : τr 0 = τr 1 := by
      simpa [τr] using hclosed.symm
    have hτrann : ∀ x ∈ Icc (0 : ℝ) 1,
        r < dist (τr x) c ∧ dist (τr x) c < 2 * r := by
      intro x hx
      exact hτann _
        (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem h1 h0 hx)
    have hMrexp : ∀ x ∈ Icc (0 : ℝ) 1,
        Complex.exp (Mr x) = τr x - c := by
      intro x hx
      exact hMexp _
        (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem h1 h0 hx)
    have hposr : 2 * Real.pi ≤ (Mr 1 - Mr 0).im := by
      simp only [Mr, SupercriticalLQGUniqueness.B2.Strong.seg]
      norm_num at *
      linarith
    obtain ⟨α, hα, hαann, hαleft, hαtop, hαbelow, hαright, hαcost⟩ :=
      laneC_positive_corner_paid_crosscut_oriented D hτr hclosedr hτrann
        hcre0 hcreNear hcim1 hTopNear hbelow hright hMr hMrexp hposr
    have hrevCost : D.len τr 0 1 ≤ D.len τ 0 1 :=
      SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
        (D.pt ∘ τ) h1 h0
    exact ⟨α, hα, hαann, hαleft, hαtop, hαbelow, hαright, hαcost.trans hrevCost⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
