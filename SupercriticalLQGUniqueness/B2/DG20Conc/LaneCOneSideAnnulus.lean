import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOneSideClip
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSideTraceInImage

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_ball_horizontal_strip
    {c z : ℂ} {r : ℝ} (hz : dist z c < 2 * r)
    (hlo : 2 * r ≤ c.im) (hhi : c.im + 2 * r ≤ 1) :
    z.im ∈ Icc (0 : ℝ) 1 := by
  have hn : ‖z - c‖ < 2 * r := by simpa [dist_eq_norm] using hz
  have hi : |z.im - c.im| < 2 * r := by
    simpa [Complex.sub_im] using
      (Complex.abs_im_le_norm (z - c)).trans_lt hn
  constructor <;> have hi' := (abs_lt.mp hi) <;> linarith

 
theorem laneC_ball_re_le_one
    {c z : ℂ} {r : ℝ} (hz : dist z c < 2 * r)
    (hhi : c.re + 2 * r ≤ 1) : z.re ≤ 1 := by
  have hn : ‖z - c‖ < 2 * r := by simpa [dist_eq_norm] using hz
  have hr : |z.re - c.re| < 2 * r := by
    simpa [Complex.sub_re] using
      (Complex.abs_re_le_norm (z - c)).trans_lt hn
  have := (abs_lt.mp hr).2
  linarith

 
theorem laneC_ball_re_nonneg
    {c z : ℂ} {r : ℝ} (hz : dist z c < 2 * r)
    (hlo : 2 * r ≤ c.re) : 0 ≤ z.re := by
  have hn : ‖z - c‖ < 2 * r := by simpa [dist_eq_norm] using hz
  have hr : |z.re - c.re| < 2 * r := by
    simpa [Complex.sub_re] using
      (Complex.abs_re_le_norm (z - c)).trans_lt hn
  have := (abs_lt.mp hr).1
  linarith

 

theorem laneC_left_one_side_detour
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
        β s ∈ Fr ∧ β s ∈ (rectAB 1 1).toSet) ∧
      β 0 ∈ (rectAB 1 1).side₁ ∧ γ t₁ = β 1 ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), γ t ∈ Fr) ∧
      D.len β 0 1 ≤ D.len ρ a b := by
  obtain ⟨α, t₁, ht₁, hα, hαFrImg, hα0, hα1, hafter, hlen⟩ :=
    laneC_left_side_trace_arc_in_image D hab hρ hsep hρFr hside
      hγ hm hmid hend hbad
  have hαFr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ Fr :=
    fun t ht => (hαFrImg t ht).1
  have hαball : ∀ t ∈ Icc (0 : ℝ) 1, dist (α t) c < 2 * r := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := (hαFrImg t ht).2
    rw [← hst]
    exact hρball s hs
  have ht₁sq : t₁ ∈ Icc (0 : ℝ) 1 := ⟨hm.1.trans ht₁.1, ht₁.2⟩
  obtain ⟨β, hβ, hβFrSq, hβ0, hβ1, hβlen⟩ :=
    laneC_clip_left_side_arc D hα hαFr hα0 (hα1 ▸ hγsq t₁ ht₁sq)
      (fun t ht => laneC_ball_horizontal_strip (hαball t ht) hclo hchi)
      (fun t ht => laneC_ball_re_le_one (hαball t ht) hcri)
  exact ⟨β, t₁, ht₁, hβ, hβFrSq, hβ0,
    hα1.trans hβ1.symm, hafter, hβlen.trans hlen⟩

 
theorem laneC_right_one_side_detour
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
        β s ∈ Fr ∧ β s ∈ (rectAB 1 1).toSet) ∧
      γ t₀ = β 0 ∧ β 1 ∈ (rectAB 1 1).side₂ ∧
      (∀ t ∈ Icc (0 : ℝ) t₀, γ t ∈ Fr) ∧
      D.len β 0 1 ≤ D.len ρ a b := by
  obtain ⟨α, t₀, ht₀, hα, hαFrImg, hα0, hα1, hbefore, hlen⟩ :=
    laneC_right_side_trace_arc_in_image D hab hρ hsep hρFr hside
      hγ hm hstart hmid hbad
  have hαFr : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ Fr :=
    fun t ht => (hαFrImg t ht).1
  have hαball : ∀ t ∈ Icc (0 : ℝ) 1, dist (α t) c < 2 * r := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := (hαFrImg t ht).2
    rw [← hst]
    exact hρball s hs
  have ht₀sq : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1, ht₀.2.trans hm.2⟩
  obtain ⟨β, hβ, hβFrSq, hβ0, hβ1, hβlen⟩ :=
    laneC_clip_right_side_arc D hα hαFr (hα0 ▸ hγsq t₀ ht₀sq) hα1
      (fun t ht => laneC_ball_horizontal_strip (hαball t ht) hclo hchi)
      (fun t ht => laneC_ball_re_nonneg (hαball t ht) hcle)
  exact ⟨β, t₀, ht₀, hβ, hβFrSq,
    hα0.trans hβ0.symm, hβ1, hbefore, hβlen.trans hlen⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
