/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AssemblyData
import InteractingSLE.Spec.Supplement.SB4RMirror

/-!
# S3's strict height comparison with the lower piece exposed on its right

Reflection negates heights and schedule angles. This file reuses the checked
upper-side contradiction after that sign change. It also gives the rational
interval reduction for a charted piece; that reduction needs no claim that
the charted piece is itself a generating trace in the original half-plane.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.S3

/-- A schedule side label reflects by negating both its value and angle. -/
theorem sideH_neg_reflAngles {κ v : ℝ} {l : List (ℝ × ℝ≥0)}
    (hv : Lh.SideH κ l v) : Lh.SideH κ (Lf.reflAngles l) (-v) := by
  obtain ⟨p, hp, hv | hv⟩ := hv
  · refine ⟨(-p.1, p.2), Lf.mem_reflAngles.2 ?_, Or.inr ?_⟩
    · simpa only [neg_neg, Prod.eta] using hp
    · rw [hv]; dsimp; ring
  · refine ⟨(-p.1, p.2), Lf.mem_reflAngles.2 ?_, Or.inl ?_⟩
    · simpa only [neg_neg, Prod.eta] using hp
    · rw [hv]; dsimp; ring

/-- Neither old side height equals the exposed right height of a strictly
lower angle. This is the already proved upper mismatch under reflection. -/
theorem sideH_ne_lower_right {κ ϑ v : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, ϑ < p.1) (hv : Lh.SideH κ l v) :
    v ≠ sleLambda κ - ϑ * chiC κ := by
  have hθR : ∀ p ∈ Lf.reflAngles l, p.1 < -ϑ := by
    intro p hp
    have h := hθ (-p.1, p.2) (Lf.mem_reflAngles.1 hp)
    dsimp at h
    linarith only [h]
  have hne := sideH_ne_upper_left hκ hκ4 hθR (sideH_neg_reflAngles hv)
  intro he
  apply hne
  rw [he]
  ring

/-- The same marked means and exact phases exclude a lower piece's common
arc. No new conditional-law or geometric reflection claim is used here. -/
theorem ProtectedWordComparison.false_lower {κ ϑ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, ϑ < p.1) {A : Set ℂ}
    {β : ℝ≥0 → ℂ} {a b : ℝ≥0}
    (d : ProtectedWordComparison κ (sleLambda κ - ϑ * chiC κ) A β a b)
    (hlabel : Lh.SideH κ l (d.word.fn d.coordinate)) : False :=
  sideH_ne_lower_right hκ hκ4 hθ hlabel d.word_value_eq

/-- For an arbitrary parametrized physical piece, every common open interval
contains a rational closed interval strictly before the lifetime. This does
not require continuity or an entrance-time premise. -/
theorem no_common_arc_of_rational_compact_piece {β : ℝ≥0 → ℂ} {A : Set ℂ}
    {ζ : ℝ≥0∞}
    (hQ : ∀ q₁ q₂ : ℚ, (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
      ((q₂ : ℝ).toNNReal : ℝ≥0∞) < ζ →
      ¬ β '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ A) :
    ∀ s₁ s₂ : ℝ≥0, s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ ζ → ¬ β '' Ioo s₁ s₂ ⊆ A := by
  intro s₁ s₂ hs hζ hA
  obtain ⟨q₁, hs₁, hq₁⟩ := Supp9.W0b.exists_rat_btwn_nnreal hs
  obtain ⟨q₂, hq₁₂, hq₂⟩ := Supp9.W0b.exists_rat_btwn_nnreal hq₁
  apply hQ q₁ q₂ hq₁₂ ((ENNReal.coe_lt_coe.2 hq₂).trans_le hζ)
  rintro z ⟨t, ht, rfl⟩
  exact hA ⟨t, ⟨hs₁.trans_le ht.1, ht.2.trans_lt hq₂⟩, rfl⟩

/-- Intersect the rational comparison events under the actual retained
measure. The launched-piece predicate need not itself be measurable. -/
theorem ae_no_common_arc_lower_of_protectedWord {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {κ ϑ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, ϑ < p.1)
    {A : Set ℂ} {β : ℕ → Ω → ℝ≥0 → ℂ} {ζ : ℕ → Ω → ℝ≥0∞}
    {launched : ℕ → Ω → Prop}
    (hW : ∀ q₁ q₂ : ℚ, ∀ᵐ ω ∂Q, ∀ j, launched j ω →
      (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
      ((q₂ : ℝ).toNNReal : ℝ≥0∞) < ζ j ω →
      β j ω '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ A →
      ∃ d : ProtectedWordComparison κ (sleLambda κ - ϑ * chiC κ) A (β j ω)
        (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal,
        Lh.SideH κ l (d.word.fn d.coordinate)) :
    ∀ᵐ ω ∂Q, ∀ j, launched j ω → ∀ s₁ s₂ : ℝ≥0,
      s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ ζ j ω → ¬ β j ω '' Ioo s₁ s₂ ⊆ A := by
  filter_upwards [ae_all_iff.2 fun q₁ => ae_all_iff.2 (hW q₁)] with ω hω
  intro j hj
  apply no_common_arc_of_rational_compact_piece
  intro q₁ q₂ hq hζ hA
  obtain ⟨d, hlabel⟩ := hω q₁ q₂ j hj hq hζ hA
  exact d.false_lower hκ hκ4 hθ hlabel

end InteractingSLE.Theorem14.SB.S3
