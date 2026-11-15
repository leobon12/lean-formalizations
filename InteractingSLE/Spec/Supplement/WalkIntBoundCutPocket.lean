/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutRun
import InteractingSLE.Spec.Supplement.PocketMirrorAssembly

/-!
# Bounded component landings strictly precede a common closing contact

The committed pocket-shape construction is used through the sector map,
so real connectors are allowed. The committed Jordan coordinate of the
shaped pocket excludes its closing endpoint at every finite coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open GW4Reg GB11Chart GW3SidedProof

/-- A component chart supplies the uniformizer needed by the existing
shape construction, without global side hypotheses on the walks. -/
theorem exists_shape_of_component_chart {α β : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α) (hβ : GB11.IsCompleteSimpleFlow β)
    (horder : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hno : ∀ a b : ℝ≥0, a < b → ¬ α '' Icc a b ⊆ range β)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β))
    {c : Chart} (hc : IsComponentChart (range α) (range β) C c) :
    ∃ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape α β C s t u v := by
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hα) (isClosed_range_of_isCompleteSimpleFlow hβ) hC
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  have hU := GW3.hasOrientedUniformizer_of_isComponentChart hc hCo hCH
  have ho : ∀ s s' t t' : ℝ≥0, (sectorMap ∘ α) s = (sectorMap ∘ β) t →
      (sectorMap ∘ α) s' = (sectorMap ∘ β) t' → (s < s' ↔ t < t') :=
    fun _ _ _ _ h h' => horder _ _ _ _ (sectorMap_injective h) (sectorMap_injective h')
  have hn : ∀ a b : ℝ≥0, a < b → ¬ (sectorMap ∘ α) '' Icc a b ⊆ range (sectorMap ∘ β) := by
    intro a b hab hsub
    apply hno a b hab
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨t, ht⟩ := hsub ⟨r, hr, rfl⟩
    exact ⟨t, sectorMap_injective ht⟩
  obtain ⟨s, t, u, v, hs⟩ :=
    (PocketRim.interiorUniformizerShapeStatement_of_discGapSide PocketMirror.discGapSideStatement)
      (sectorMap ∘ α) (sectorMap ∘ β)
      (PocketSector.isSimpleProper_sector hα) (PocketSector.isSimpleProper_sector hβ) ho hn
      (sectorMap '' C) (PocketSector.image_mem_between hα hβ hC)
      (PocketSector.hasOrientedUniformizer_sector_image hα hβ hC hU)
  exact ⟨s, t, u, v, PocketSector.shape_of_sector_image hα hβ hC hs⟩

/-- Every finite real boundary landing of a pocket coordinate lies in
the component closure and avoids its excluded endpoint set. -/
theorem landing_mem_of_pocketCoord {α β : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart}
    {s t : ℝ≥0} {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}
    (h : IsPocketCoord α β C c s t E ψ G k) {x : ℝ} {p : ℂ}
    (hp : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) : p ∈ closure C \ E := by
  have hx : (k : ℂ) * (x : ℂ) ∈ Hbar := by
    change 0 ≤ ((k : ℂ) * (x : ℂ)).im
    simp only [Complex.mul_im, Complex.ofReal_im, zero_mul, mul_zero, add_zero, le_refl]
  have hm : Tendsto (fun w : ℂ => (k : ℂ) * w) (𝓝[H] (x : ℂ))
      (𝓝[Hbar] ((k : ℂ) * (x : ℂ))) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨(continuous_const.mul continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    change 0 ≤ ((k : ℂ) * w).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      (mul_nonneg h.pos.le (show 0 < w.im from hw).le)
  have hlim : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (G ((k : ℂ) * (x : ℂ)))) :=
    ((h.continuousOn_G _ hx).tendsto.comp hm).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (h.inv_eq w hw).symm)
  have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  exact (tendsto_nhds_unique hp hlim).symm ▸ h.mapsTo_G hx

end InteractingSLE.Theorem14.WalkIntBoundCut
