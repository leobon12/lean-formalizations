import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSideSafeFirstHit
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOneSidedHit
import SupercriticalLQGUniqueness.B2.Strong.Glue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set LQGMetric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem laneC_no_side_continuous_separator_arc
    (D : ContMetric) {E F Fr U S : Set ℂ}
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b) E F)
    (hρFr : ∀ s ∈ Icc a b, ρ s ∈ Fr)
    (hρU : ∀ s ∈ Icc a b, ρ s ∈ U)
    (hno : (ρ '' Icc a b) ∩ S = ∅)
    {y : ℂ} (hyF : y ∈ F) (hside : Path y (γ 0))
    (hsideS : ∀ t, hside t ∈ S)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : γ m ∈ E) (hend : γ 1 ∈ F)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ (α : ℝ → ℂ) (t₀ t₁ : ℝ),
      t₀ ∈ Icc (0 : ℝ) 1 ∧ t₁ ∈ Icc (0 : ℝ) 1 ∧ t₀ ≤ t₁ ∧
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, α s ∈ Fr ∧ α s ∈ U) ∧
      γ t₀ = α 0 ∧ γ t₁ = α 1 ∧
      (∀ t ∈ Icc (0 : ℝ) t₀, γ t ∈ Fr) ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), γ t ∈ Fr) ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  have hXclosed : IsClosed (ρ '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hρ).isClosed
  have hXFr : (ρ '' Icc a b) ⊆ Fr := by
    rintro z ⟨s, hs, rfl⟩
    exact hρFr s hs
  obtain ⟨t₀, ht₀, hhit₀, hbefore⟩ :=
    laneC_first_separator_hit_of_side_path hXclosed hsep hXFr
      hno hyF hside hsideS hγ hm hmid hbad
  obtain ⟨t₁, ht₁, hhit₁, hafter⟩ :=
    laneC_last_separator_hit hXclosed hsep hXFr hγ hm hmid hend hbad
  obtain ⟨s₀, hs₀, hs₀eq⟩ := hhit₀
  obtain ⟨s₁, hs₁, hs₁eq⟩ := hhit₁
  let α := SupercriticalLQGUniqueness.B2.Strong.seg ρ s₀ s₁
  refine ⟨α, t₀, t₁, ⟨ht₀.1, ht₀.2.trans hm.2⟩,
    ⟨hm.1.trans ht₁.1, ht₁.2⟩, ht₀.2.trans ht₁.1,
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ hs₀ hs₁,
    ?_, ?_, ?_, hbefore, hafter, ?_⟩
  · intro s hs
    have hp := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs₀ hs₁ hs
    exact ⟨hρFr _ hp, hρU _ hp⟩
  · simpa only [α, SupercriticalLQGUniqueness.B2.Strong.seg,
      zero_mul, add_zero] using hs₀eq.symm
  · convert hs₁eq.symm using 1
    dsimp [α, SupercriticalLQGUniqueness.B2.Strong.seg]
    ring
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ ρ) hs₀ hs₁

end SupercriticalLQGUniqueness.B2.DG20Conc
