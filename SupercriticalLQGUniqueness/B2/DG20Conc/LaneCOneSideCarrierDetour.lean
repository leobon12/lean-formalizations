import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOneSideAnnulus

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_left_one_side_detour_in_image
    (D : ContMetric) {E F Fr : Set ℂ} {c : ℂ} {r : ℝ}
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b) E F)
    (hρFr : ∀ s ∈ Icc a b, ρ s ∈ Fr)
    (hρball : ∀ s ∈ Icc a b, dist (ρ s) c < 2 * r)
    (hside : ((ρ '' Icc a b) ∩ (rectAB 1 1).side₁).Nonempty)
    (hclo : 2 * r ≤ c.im) (hchi : c.im + 2 * r ≤ 1)
    (hcri : c.re + 2 * r ≤ 1)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγsq : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : γ m ∈ E) (hend : γ 1 ∈ F)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ (β : ℝ → ℂ) (t₁ : ℝ),
      t₁ ∈ Icc m (1 : ℝ) ∧
      ContinuousOn β (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        β s ∈ Fr ∧ β s ∈ (rectAB 1 1).toSet ∧
          β s ∈ ρ '' Icc a b) ∧
      β 0 ∈ (rectAB 1 1).side₁ ∧ γ t₁ = β 1 ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), γ t ∈ Fr) ∧
      D.len β 0 1 ≤ D.len ρ a b := by
  obtain ⟨α, t₁, ht₁, hα, hαFrImg, hα0, hα1, hafter, hlen⟩ :=
    laneC_left_side_trace_arc_in_image D hab hρ hsep hρFr hside
      hγ hm hmid hend hbad
  have ht₁sq : t₁ ∈ Icc (0 : ℝ) 1 := ⟨hm.1.trans ht₁.1, ht₁.2⟩
  have hα1sq : α 1 ∈ (rectAB 1 1).toSet := hα1 ▸ hγsq t₁ ht₁sq
  have hzero : (α 0).re = 0 := (mem_rectAB_side₁.mp hα0).1
  have hone : 0 ≤ (α 1).re := (mem_rectAB_toSet.mp hα1sq).1.1
  obtain ⟨u, hu, huz, hafterZero⟩ :=
    laneC_exists_last_zero_nonneg zero_le_one
      (Complex.continuous_re.comp_continuousOn hα) hzero hone
  let β := SupercriticalLQGUniqueness.B2.Strong.seg α u 1
  have hβ : ContinuousOn β (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hα hu
      (show (1 : ℝ) ∈ Icc 0 1 by simp)
  have hβ0 : β 0 = α u := by simp [β]
  have hβ1 : β 1 = α 1 := by
    dsimp [β, SupercriticalLQGUniqueness.B2.Strong.seg]
    congr 1
    ring
  refine ⟨β, t₁, ht₁, hβ, ?_, ?_, hα1.trans hβ1.symm,
    hafter, ?_⟩
  · intro t ht
    have hp := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem
      hu (show (1 : ℝ) ∈ Icc 0 1 by simp) ht
    have hp' : u + t * (1 - u) ∈ Icc u (1 : ℝ) := by
      constructor
      · have h0 : 0 ≤ t := ht.1
        have h1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
        nlinarith [mul_nonneg h0 h1]
      · exact hp.2
    have hnonneg : 0 ≤ (β t).re := by
      simpa [β, SupercriticalLQGUniqueness.B2.Strong.seg] using
        hafterZero (u + t * (1 - u)) hp'
    have hαball : dist (β t) c < 2 * r := by
      obtain ⟨s, hs, hst⟩ := (hαFrImg _ hp).2
      change dist (α (u + t * (1 - u))) c < 2 * r
      rw [← hst]
      exact hρball s hs
    have hsq : β t ∈ (rectAB 1 1).toSet := by
      apply mem_rectAB_toSet.mpr
      exact ⟨⟨hnonneg, laneC_ball_re_le_one hαball hcri⟩,
        laneC_ball_horizontal_strip hαball hclo hchi⟩
    exact ⟨(hαFrImg _ hp).1, hsq, (hαFrImg _ hp).2⟩
  · rw [hβ0, mem_rectAB_side₁]
    have hαball : dist (α u) c < 2 * r := by
      obtain ⟨s, hs, hst⟩ := (hαFrImg u hu).2
      rw [← hst]
      exact hρball s hs
    exact ⟨huz, laneC_ball_horizontal_strip hαball hclo hchi⟩
  · exact (SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ α) hu (show (1 : ℝ) ∈ Icc 0 1 by simp)).trans hlen

 
theorem laneC_right_one_side_detour_in_image
    (D : ContMetric) {E F Fr : Set ℂ} {c : ℂ} {r : ℝ}
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b) E F)
    (hρFr : ∀ s ∈ Icc a b, ρ s ∈ Fr)
    (hρball : ∀ s ∈ Icc a b, dist (ρ s) c < 2 * r)
    (hside : ((ρ '' Icc a b) ∩ (rectAB 1 1).side₂).Nonempty)
    (hclo : 2 * r ≤ c.im) (hchi : c.im + 2 * r ≤ 1)
    (hcle : 2 * r ≤ c.re)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγsq : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hstart : γ 0 ∈ F) (hmid : γ m ∈ E)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ (β : ℝ → ℂ) (t₀ : ℝ),
      t₀ ∈ Icc (0 : ℝ) m ∧
      ContinuousOn β (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        β s ∈ Fr ∧ β s ∈ (rectAB 1 1).toSet ∧
          β s ∈ ρ '' Icc a b) ∧
      γ t₀ = β 0 ∧ β 1 ∈ (rectAB 1 1).side₂ ∧
      (∀ t ∈ Icc (0 : ℝ) t₀, γ t ∈ Fr) ∧
      D.len β 0 1 ≤ D.len ρ a b := by
  obtain ⟨α, t₀, ht₀, hα, hαFrImg, hα0, hα1, hbefore, hlen⟩ :=
    laneC_right_side_trace_arc_in_image D hab hρ hsep hρFr hside
      hγ hm hstart hmid hbad
  have ht₀sq : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1, ht₀.2.trans hm.2⟩
  have hα0sq : α 0 ∈ (rectAB 1 1).toSet := hα0 ▸ hγsq t₀ ht₀sq
  have hzero : (α 1).re = 1 := (mem_rectAB_side₂.mp hα1).1
  have hone : (α 0).re ≤ 1 := (mem_rectAB_toSet.mp hα0sq).1.2
  obtain ⟨u, hu, huz, hbeforeZero⟩ :=
    laneC_exists_first_zero_nonneg zero_le_one
      (continuousOn_const.sub (Complex.continuous_re.comp_continuousOn hα))
      (by change 0 ≤ 1 - (α 0).re; linarith)
      (by change 1 - (α 1).re = 0; linarith)
  let β := SupercriticalLQGUniqueness.B2.Strong.seg α 0 u
  have hβ : ContinuousOn β (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hα
      (show (0 : ℝ) ∈ Icc 0 1 by simp) hu
  have hβ0 : β 0 = α 0 := by simp [β]
  have hβ1 : β 1 = α u := by
    dsimp [β, SupercriticalLQGUniqueness.B2.Strong.seg]
    congr 1
    ring
  refine ⟨β, t₀, ht₀, hβ, ?_, hα0.trans hβ0.symm,
    ?_, hbefore, ?_⟩
  · intro t ht
    have hp := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem
      (show (0 : ℝ) ∈ Icc 0 1 by simp) hu ht
    have hp' : t * u ∈ Icc (0 : ℝ) u := by
      have hu0 : 0 ≤ u := hu.1
      constructor
      · exact mul_nonneg ht.1 hu0
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hu0]
    have hupper : (β t).re ≤ 1 := by
      have h := hbeforeZero (t * u) hp'
      change 0 ≤ 1 - (α (t * u)).re at h
      have h' : 0 ≤ 1 - (β t).re := by
        simpa [β, SupercriticalLQGUniqueness.B2.Strong.seg] using h
      linarith
    have hαball : dist (β t) c < 2 * r := by
      obtain ⟨s, hs, hst⟩ := (hαFrImg _ hp).2
      have hh : dist (α (t * u)) c < 2 * r := by
        simpa [hst] using hρball s hs
      simpa [β, SupercriticalLQGUniqueness.B2.Strong.seg] using hh
    have hsq : β t ∈ (rectAB 1 1).toSet := by
      apply mem_rectAB_toSet.mpr
      exact ⟨⟨laneC_ball_re_nonneg hαball hcle, hupper⟩,
        laneC_ball_horizontal_strip hαball hclo hchi⟩
    exact ⟨(hαFrImg _ hp).1, hsq, (hαFrImg _ hp).2⟩
  · rw [hβ1, mem_rectAB_side₂]
    have hαball : dist (α u) c < 2 * r := by
      obtain ⟨s, hs, hst⟩ := (hαFrImg u hu).2
      rw [← hst]
      exact hρball s hs
    constructor
    · change 1 - (α u).re = 0 at huz
      linarith
    · exact laneC_ball_horizontal_strip hαball hclo hchi
  · exact (SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ α) (show (0 : ℝ) ∈ Icc 0 1 by simp) hu).trans hlen

end SupercriticalLQGUniqueness.B2.DG20Conc
