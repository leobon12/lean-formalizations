import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOneSidedHit
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCContinuousInteriorSurgery

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set LQGMetric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 



theorem laneC_left_side_trace_arc
    (D : ContMetric) {E F Fr S : Set ℂ}
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b) E F)
    (hρFr : ∀ s ∈ Icc a b, ρ s ∈ Fr)
    (hside : ((ρ '' Icc a b) ∩ S).Nonempty)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : γ m ∈ E) (hend : γ 1 ∈ F)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ (α : ℝ → ℂ) (t₁ : ℝ),
      t₁ ∈ Icc m (1 : ℝ) ∧
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, α s ∈ Fr) ∧
      α 0 ∈ S ∧ γ t₁ = α 1 ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), γ t ∈ Fr) ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  have hXclosed : IsClosed (ρ '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hρ).isClosed
  obtain ⟨t₁, ht₁, hhit, hafter⟩ :=
    laneC_last_separator_hit hXclosed hsep
      (by rintro x ⟨s, hs, rfl⟩; exact hρFr s hs)
      hγ hm hmid hend hbad
  obtain ⟨_, ⟨s₀, hs₀, hs₀eq⟩, hs₀S⟩ := hside
  obtain ⟨s₁, hs₁, hs₁eq⟩ := hhit
  let α := SupercriticalLQGUniqueness.B2.Strong.seg ρ s₀ s₁
  refine ⟨α, t₁, ht₁,
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ hs₀ hs₁,
    ?_, ?_, ?_, hafter, ?_⟩
  · intro s hs
    exact hρFr _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs₀ hs₁ hs)
  · simpa only [α, SupercriticalLQGUniqueness.B2.Strong.seg,
      zero_mul, add_zero] using (hs₀eq ▸ hs₀S)
  · convert hs₁eq.symm using 1
    dsimp [α, SupercriticalLQGUniqueness.B2.Strong.seg]
    ring
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ ρ) hs₀ hs₁

 
theorem laneC_right_side_trace_arc
    (D : ContMetric) {E F Fr S : Set ℂ}
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b) E F)
    (hρFr : ∀ s ∈ Icc a b, ρ s ∈ Fr)
    (hside : ((ρ '' Icc a b) ∩ S).Nonempty)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hstart : γ 0 ∈ F) (hmid : γ m ∈ E)
    (hbad : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ Fr → γ t ∈ E) :
    ∃ (α : ℝ → ℂ) (t₀ : ℝ),
      t₀ ∈ Icc (0 : ℝ) m ∧
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, α s ∈ Fr) ∧
      γ t₀ = α 0 ∧ α 1 ∈ S ∧
      (∀ t ∈ Icc (0 : ℝ) t₀, γ t ∈ Fr) ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  have hXclosed : IsClosed (ρ '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hρ).isClosed
  obtain ⟨t₀, ht₀, hhit, hbefore⟩ :=
    laneC_first_separator_hit hXclosed hsep
      (by rintro x ⟨s, hs, rfl⟩; exact hρFr s hs)
      hγ hm hstart hmid hbad
  obtain ⟨_, ⟨s₁, hs₁, hs₁eq⟩, hs₁S⟩ := hside
  obtain ⟨s₀, hs₀, hs₀eq⟩ := hhit
  let α := SupercriticalLQGUniqueness.B2.Strong.seg ρ s₀ s₁
  refine ⟨α, t₀, ht₀,
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hρ hs₀ hs₁,
    ?_, ?_, ?_, hbefore, ?_⟩
  · intro s hs
    exact hρFr _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem hs₀ hs₁ hs)
  · simpa only [α, SupercriticalLQGUniqueness.B2.Strong.seg,
      zero_mul, add_zero] using hs₀eq.symm
  · have : α 1 = ρ s₁ := by
      dsimp [α, SupercriticalLQGUniqueness.B2.Strong.seg]
      congr 1
      ring
    rw [this]
    exact hs₁eq ▸ hs₁S
  · exact SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ ρ) hs₀ hs₁

end SupercriticalLQGUniqueness.B2.DG20Conc
