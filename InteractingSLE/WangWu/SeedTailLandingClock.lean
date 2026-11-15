/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailLandingGap

/-!
# Terminal limits and the killed arc's capacity parametrization

PROVE-WW-B27. The order filter on the pre-contact interval treats finite contact
and infinite escape uniformly. A finite terminal curve limit bounds the entire
arc and transfers to the capacity trace at its finite positive lifetime.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu.SeedTail

open ImgWord Sec7.Lemma71C

/-- Approaching the right end of an interval, whether finite or infinite. -/
def arcEnd (P : Set ℝ) : Filter ℝ := Filter.map (fun t : P => (t : ℝ)) atTop

theorem mem_arcEnd_iff {γ : ℝ → ℂ} {P A : Set ℝ} (hγ : IsKilledArc γ P) :
    A ∈ arcEnd P ↔ ∃ a ∈ P, ∀ b ∈ P, a ≤ b → b ∈ A := by
  have : Nonempty P := ⟨⟨0, hγ.zero_mem⟩⟩
  change (∀ᶠ a : P in atTop, (a : ℝ) ∈ A) ↔ _
  rw [eventually_atTop]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, a.2, fun b hb hab => ha ⟨b, hb⟩ hab⟩
  · rintro ⟨a, ha, hA⟩
    exact ⟨⟨a, ha⟩, fun b hab => hA b b.2 hab⟩

/-- The inverse capacity clock approaches the full pre-contact interval. -/
theorem tendsto_kInv_arcEnd {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {τ : ℝ≥0} (hτ : (τ : WithTop ℝ≥0) = kLife γ P) :
    Tendsto (fun t : ℝ≥0 => kInv γ P t) (𝓝[<] τ) (arcEnd P) := by
  intro A hA
  obtain ⟨a, ha, hA⟩ := (mem_arcEnd_iff hγ).1 hA
  have haτ : (capClock γ a).toNNReal < τ := by
    have h := hγ.lt_kLife ha
    rw [← hτ] at h
    exact_mod_cast h
  change ∀ᶠ t : ℝ≥0 in 𝓝[<] τ, kInv γ P t ∈ A
  filter_upwards [Ioo_mem_nhdsLT haτ] with t ht
  have htL : (t : WithTop ℝ≥0) < kLife γ P := by rw [← hτ]; exact_mod_cast ht.2
  obtain ⟨hi, he⟩ := hγ.kInv_spec htL
  apply hA _ hi
  apply (hγ.strictMonoOn_capClock.le_iff_le ha hi).1
  rw [he]
  have h := NNReal.coe_le_coe.2 ht.1.le
  rwa [Real.coe_toNNReal _ (hγ.capClock_nonneg ha)] at h

/-- A finite terminal limit bounds the whole killed arc. -/
theorem isBounded_image_of_arcEnd_limit {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {z : ℂ} (hz : Tendsto γ (arcEnd P) (𝓝 z)) : IsBounded (γ '' P) := by
  obtain ⟨a, ha, hA⟩ := (mem_arcEnd_iff hγ).1 (hz (ball_mem_nhds z one_pos))
  have hC := isCompact_Icc.image_of_continuousOn (hγ.cont.mono (hγ.icc a ha))
  apply (hC.isBounded.union (isBounded_ball (x := z) (r := 1))).subset
  rintro _ ⟨b, hb, rfl⟩
  rcases le_or_gt b a with hba | hab
  · exact Or.inl ⟨b, ⟨hγ.nonneg b hb, hba⟩, rfl⟩
  · exact Or.inr (hA b hb hab.le)

/-- A finite terminal limit transfers to the capacity trace, and its lifetime
is finite and strictly positive. -/
theorem exists_kTrace_limit_of_arcEnd_limit {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledArc γ P)
    {z : ℂ} (hz : Tendsto γ (arcEnd P) (𝓝 z)) :
    ∃ τ : ℝ≥0, 0 < τ ∧ (τ : WithTop ℝ≥0) = kLife γ P ∧
      Tendsto (kTrace γ P) (𝓝[<] τ) (𝓝 z) := by
  obtain ⟨τ, hτ0, hτ⟩ := exists_finite_kLife_of_isBounded hγ (isBounded_image_of_arcEnd_limit hγ hz)
  exact ⟨τ, hτ0, hτ, hz.comp (tendsto_kInv_arcEnd hγ hτ)⟩

end InteractingSLE.WangWu.SeedTail
