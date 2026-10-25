import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCFirstLastHit
import SupercriticalLQGUniqueness.B2.Strong.Glue

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 


theorem laneC_continuous_interior_separator_arc
    (D : ContMetric) {E F Fr U : Set ℂ}
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hsep : Disconnects (ρ '' Icc a b) E F)
    (hρFr : ∀ s ∈ Icc a b, ρ s ∈ Fr)
    (hρU : ∀ s ∈ Icc a b, ρ s ∈ U)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hstart : γ 0 ∈ F) (hmid : γ m ∈ E) (hend : γ 1 ∈ F)
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
  obtain ⟨t₀, ht₀, t₁, ht₁, hhit₀, hhit₁, hbefore, hafter⟩ :=
    laneC_first_last_separator_hits hXclosed hsep
      (by rintro x ⟨s, hs, rfl⟩; exact hρFr s hs)
      hγ hm hstart hmid hend hbad
  obtain ⟨s₀, hs₀, hs₀eq⟩ := hhit₀
  obtain ⟨s₁, hs₁, hs₁eq⟩ := hhit₁
  let α := SupercriticalLQGUniqueness.B2.Strong.seg ρ s₀ s₁
  refine ⟨α, t₀, t₁, ⟨ht₀.1, ht₀.2.trans hm.2⟩,
    ⟨hm.1.trans ht₁.1, ht₁.2⟩, ht₀.2.trans ht₁.1,
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ hs₀ hs₁,
    ?_, ?_, ?_, hbefore, hafter, ?_⟩
  · intro s hs
    have hparam := SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs₀ hs₁ hs
    exact ⟨hρFr _ hparam, hρU _ hparam⟩
  · simpa only [α, SupercriticalLQGUniqueness.B2.Strong.seg,
      zero_mul, add_zero] using hs₀eq.symm
  · convert hs₁eq.symm using 1
    dsimp [α, SupercriticalLQGUniqueness.B2.Strong.seg]
    ring
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ ρ) hs₀ hs₁

end SupercriticalLQGUniqueness.B2.DG20Conc
