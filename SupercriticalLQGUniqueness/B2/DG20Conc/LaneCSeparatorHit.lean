import LQGMetric.Topo.Shortcut

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open Set LQGMetric

 
theorem laneC_separator_meets_subpath {X E F : Set ℂ}
    (hsep : Disconnects X E F) {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (ha : γ a ∈ E) (hb : γ b ∈ F) :
    ∃ t ∈ Icc a b, γ t ∈ X := by
  obtain ⟨x, hx, hxX⟩ := hsep (γ a) (γ b) (pathOfIcc γ hab hγ) ha hb
  obtain ⟨t, ht, htx⟩ := range_pathOfIcc_subset γ hab hγ hx
  exact ⟨t, ht, htx ▸ hxX⟩

 

theorem laneC_separator_two_ordered_hits {X E F : Set ℂ}
    (hsep : Disconnects X E F) {γ : ℝ → ℂ} {a m b : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (ha : γ a ∈ F) (hm : γ m ∈ E) (hb : γ b ∈ F) :
    ∃ t₀ ∈ Icc a m, ∃ t₁ ∈ Icc m b,
      t₀ ≤ t₁ ∧ γ t₀ ∈ X ∧ γ t₁ ∈ X := by
  have hleft := laneC_separator_meets_subpath hsep.symm ham
    (hγ.mono (Icc_subset_Icc le_rfl hmb)) ha hm
  have hright := laneC_separator_meets_subpath hsep hmb
    (hγ.mono (Icc_subset_Icc ham le_rfl)) hm hb
  obtain ⟨t₀, ht₀, hX₀⟩ := hleft
  obtain ⟨t₁, ht₁, hX₁⟩ := hright
  exact ⟨t₀, ht₀, t₁, ht₁, ht₀.2.trans ht₁.1, hX₀, hX₁⟩

 



theorem laneC_separator_two_lifted_hits {E F : Set ℂ}
    (D : ContMetric) {ρ γ : ℝ → ℂ} {c d a m b : ℝ}
    (hsep : Disconnects (ρ '' Icc c d) E F)
    (ham : a ≤ m) (hmb : m ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (ha : γ a ∈ F) (hm : γ m ∈ E) (hb : γ b ∈ F) :
    ∃ t₀ ∈ Icc a m, ∃ t₁ ∈ Icc m b,
      ∃ s₀ ∈ Icc c d, ∃ s₁ ∈ Icc c d,
        t₀ ≤ t₁ ∧ γ t₀ = ρ s₀ ∧ γ t₁ = ρ s₁ ∧
          D.len ρ (min s₀ s₁) (max s₀ s₁) ≤ D.len ρ c d := by
  obtain ⟨t₀, ht₀, t₁, ht₁, htord, ⟨s₀, hs₀, hs₀eq⟩,
      ⟨s₁, hs₁, hs₁eq⟩⟩ :=
    laneC_separator_two_ordered_hits hsep ham hmb hγ ha hm hb
  refine ⟨t₀, ht₀, t₁, ht₁, s₀, hs₀, s₁, hs₁,
    htord, hs₀eq.symm, hs₁eq.symm, ?_⟩
  exact MetricGeometry.curveLength_mono (D.pt ∘ ρ)
    (le_min hs₀.1 hs₁.1) (max_le hs₀.2 hs₁.2)

end SupercriticalLQGUniqueness.B2.DG20Conc
