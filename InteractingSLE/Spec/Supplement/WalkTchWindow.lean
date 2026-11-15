/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkContinuum

/-!
# Windows of a simple arc inside a proper walk curve

Packet PROVE-WALK-TOUCH. Two topological facts about a piece `g` (continuous and injective on a compact time interval
`[a, b]`) of a walk whose range is that of a proper simple curve `γ` (`Supp9B.IsProperCurve`):

* **`isPreconnected_inter_preimage`**: the times of a preconnected subset of `g([a, b])` form a preconnected set (`g`
  is a closed embedding of the compact interval);
* **`exists_ball_phys_window`**: near an interior point `g(t₀)`, `a < t₀ < b`, every point of the walk is a point of
  `g([a, b])`. Proof: `γ` is a closed embedding (`WalkCont.isClosedEmbedding_of_isProperCurve`), so the parameters of
  `g([a, t₀])` and of `g([t₀, b])` are intervals; by injectivity of `g` the parameter of `g(t₀)` lies strictly between
  those of `g(a)` and `g(b)`, and the image under `γ` of the complement of that open parameter interval is a closed set
  missing `g(t₀)`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkTch

/-- **Times of a preconnected subset of a simple arc form a preconnected set.** -/
theorem isPreconnected_inter_preimage {g : ℝ≥0 → ℂ} {a b : ℝ≥0} (hgc : ContinuousOn g (Icc a b))
    (hgi : InjOn g (Icc a b)) {S : Set ℂ} (hS : IsPreconnected S) (hSg : S ⊆ g '' Icc a b) :
    IsPreconnected (Icc a b ∩ g ⁻¹' S) := by
  have : CompactSpace (Icc a b) := isCompact_iff_compactSpace.1 isCompact_Icc
  set G : Icc a b → ℂ := fun t => g t with hG
  have hGc : Continuous G := continuousOn_iff_continuous_domRestrict.1 hgc
  have hGi : Function.Injective G := fun t t' h => Subtype.ext (hgi t.2 t'.2 h)
  have he : IsClosedEmbedding G := hGc.isClosedEmbedding hGi
  have hrange : range G = g '' Icc a b := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hT : IsPreconnected (G ⁻¹' S) := by
    refine he.isInducing.isPreconnected_image.1 ?_
    rw [image_preimage_eq_of_subset (hrange ▸ hSg)]
    exact hS
  have himg : Subtype.val '' (G ⁻¹' S) = Icc a b ∩ g ⁻¹' S := by
    ext t
    constructor
    · rintro ⟨t', ht', rfl⟩
      exact ⟨t'.2, ht'⟩
    · rintro ⟨ht, hS'⟩
      exact ⟨⟨t, ht⟩, hS', rfl⟩
  rw [← himg]
  exact hT.image _ continuous_subtype_val.continuousOn

/-- **The physical window of an interior arc point** (see the module docstring). -/
theorem exists_ball_phys_window {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) {g : ℝ≥0 → ℂ} {a b t₀ : ℝ≥0}
    (hat : a < t₀) (htb : t₀ < b) (hgc : ContinuousOn g (Icc a b)) (hgi : InjOn g (Icc a b))
    (hgγ : g '' Icc a b ⊆ range γ) :
    ∃ r > 0, ∀ z ∈ range γ ∩ ball (g t₀) r, ∃ t ∈ Icc a b, z = g t := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hγ
  have hab : a ≤ b := hat.le.trans htb.le
  have hsub : ∀ {a' b' : ℝ≥0}, a ≤ a' → b' ≤ b → Icc a' b' ⊆ Icc a b := fun h1 h2 t ht =>
    ⟨h1.trans ht.1, ht.2.trans h2⟩
  have hconn : ∀ {a' b' : ℝ≥0}, a ≤ a' → b' ≤ b → IsPreconnected (γ ⁻¹' (g '' Icc a' b')) := by
    intro a' b' h1 h2
    refine he.isInducing.isPreconnected_image.1 ?_
    rw [image_preimage_eq_of_subset ((image_mono (hsub h1 h2)).trans hgγ)]
    exact isPreconnected_Icc.image _ (hgc.mono (hsub h1 h2))
  have htime : ∀ {a' b' : ℝ≥0}, a ≤ a' → b' ≤ b → ∀ {v t : ℝ≥0}, t ∈ Icc a b → γ v = g t →
      v ∈ γ ⁻¹' (g '' Icc a' b') → t ∈ Icc a' b' := by
    intro a' b' h1 h2 v t ht hvt hv
    obtain ⟨t', ht', he'⟩ := hv
    have := hgi (hsub h1 h2 ht') ht (he'.trans hvt)
    rw [← this]; exact ht'
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have ht₀ : t₀ ∈ Icc a b := ⟨hat.le, htb.le⟩
  obtain ⟨va, hva⟩ := hgγ ⟨a, ha, rfl⟩
  obtain ⟨vb, hvb⟩ := hgγ ⟨b, hb, rfl⟩
  obtain ⟨vp, hvp⟩ := hgγ ⟨t₀, ht₀, rfl⟩
  have hI₁ := hconn (a' := a) (b' := t₀) le_rfl htb.le
  have hI₂ := hconn (a' := t₀) (b' := b) hat.le le_rfl
  have hva₁ : va ∈ γ ⁻¹' (g '' Icc a t₀) := ⟨a, ⟨le_rfl, hat.le⟩, hva.symm⟩
  have hvp₁ : vp ∈ γ ⁻¹' (g '' Icc a t₀) := ⟨t₀, ⟨hat.le, le_rfl⟩, hvp.symm⟩
  have hvp₂ : vp ∈ γ ⁻¹' (g '' Icc t₀ b) := ⟨t₀, ⟨le_rfl, htb.le⟩, hvp.symm⟩
  have hvb₂ : vb ∈ γ ⁻¹' (g '' Icc t₀ b) := ⟨b, ⟨htb.le, le_rfl⟩, hvb.symm⟩
  have hna : va ≠ vp := fun h => hat.ne (hgi ha ht₀ (by rw [← hva, ← hvp, h]))
  have hnb : vb ≠ vp := fun h => htb.ne' (hgi hb ht₀ (by rw [← hvb, ← hvp, h]))
  -- `b` is not a time of `g([a, t₀])`, nor `a` one of `g([t₀, b])`
  have hb₁ : vb ∉ γ ⁻¹' (g '' Icc a t₀) := fun h =>
    absurd (htime le_rfl htb.le hb hvb h).2 (not_le.2 htb)
  have ha₂ : va ∉ γ ⁻¹' (g '' Icc t₀ b) := fun h =>
    absurd (htime hat.le le_rfl ha hva h).1 (not_le.2 hat)
  have hbetween : min va vb < vp ∧ vp < max va vb := by
    rcases lt_or_gt_of_ne hna with h1 | h1 <;> rcases lt_or_gt_of_ne hnb with h2 | h2
    · exfalso
      rcases le_total va vb with h3 | h3
      · exact hb₁ (hI₁.Icc_subset hva₁ hvp₁ ⟨h3, h2.le⟩)
      · exact ha₂ (hI₂.Icc_subset hvb₂ hvp₂ ⟨h3, h1.le⟩)
    · exact ⟨lt_of_le_of_lt (min_le_left _ _) h1, lt_of_lt_of_le h2 (le_max_right _ _)⟩
    · exact ⟨lt_of_le_of_lt (min_le_right _ _) h2, lt_of_lt_of_le h1 (le_max_left _ _)⟩
    · exfalso
      rcases le_total va vb with h3 | h3
      · exact ha₂ (hI₂.Icc_subset hvp₂ hvb₂ ⟨h1.le, h3⟩)
      · exact hb₁ (hI₁.Icc_subset hvp₁ hva₁ ⟨h2.le, h3⟩)
  set K : Set ℂ := γ '' (Ioo (min va vb) (max va vb))ᶜ with hK
  have hKc : IsClosed K := he.isClosedMap _ isOpen_Ioo.isClosed_compl
  have hpK : g t₀ ∉ K := by
    rintro ⟨v, hv, hve⟩
    rw [← hvp] at hve
    rw [he.injective hve] at hv
    exact hv hbetween
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl _ hpK
  refine ⟨r, hr, ?_⟩
  rintro z ⟨⟨v, rfl⟩, hzb⟩
  have hvI : v ∈ Ioo (min va vb) (max va vb) := by
    by_contra hv
    exact hball hzb ⟨v, hv, rfl⟩
  have hI := hconn (a' := a) (b' := b) le_rfl le_rfl
  have hva' : va ∈ γ ⁻¹' (g '' Icc a b) := ⟨a, ha, hva.symm⟩
  have hvb' : vb ∈ γ ⁻¹' (g '' Icc a b) := ⟨b, hb, hvb.symm⟩
  have hsubI : Icc (min va vb) (max va vb) ⊆ γ ⁻¹' (g '' Icc a b) := by
    rcases le_total va vb with h | h
    · rw [min_eq_left h, max_eq_right h]; exact hI.Icc_subset hva' hvb'
    · rw [min_eq_right h, max_eq_left h]; exact hI.Icc_subset hvb' hva'
  obtain ⟨t, ht, hte⟩ := hsubI (Ioo_subset_Icc_self hvI)
  exact ⟨t, ht, hte.symm⟩

end InteractingSLE.Theorem14.WalkTch
