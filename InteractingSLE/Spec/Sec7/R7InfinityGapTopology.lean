/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapCollars

/-!
# The compact gate lemma with unordered or equal gates

PROVE-R7-GAPEQ. Reuse the landed gate separation for distinct gates. Equal gates
follow directly from the closed inner-face boundary and open-arm avoidance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 R7InfinityChart

/-- A compact gap path has equal endpoint values, including the case in which
its two real gates coincide. No assertion about swallowed outer prefixes is used. -/
theorem compact_gate_eq {b₁ b₂ δ : ℝ → ℂ} {x₁ x₂ a b : ℝ}
    (hx₁ : x₁ < 0) (hx₂ : x₂ < 0)
    (hc₁ : ContinuousOn b₁ (Icc 0 1)) (hc₂ : ContinuousOn b₂ (Icc 0 1))
    (hi₁ : InjOn b₁ (Icc 0 1)) (hi₂ : InjOn b₂ (Icc 0 1))
    (hz₁ : b₁ 0 = x₁) (hz₂ : b₂ 0 = x₂) (ho₁ : b₁ 1 = 0) (ho₂ : b₂ 1 = 0)
    (hH₁ : ∀ v ∈ Ioo (0 : ℝ) 1, b₁ v ∈ H) (hH₂ : ∀ v ∈ Ioo (0 : ℝ) 1, b₂ v ∈ H)
    (hdisj : ∀ w ∈ b₁ '' Ioo 0 1, w ∉ b₂ '' Ioo 0 1)
    (hab : a < b) (hδ : ContinuousOn δ (Icc a b)) (hδH : MapsTo δ (Icc a b) Hbar)
    (hF : ∀ t ∈ Icc a b, δ t ∉ innerSide (compactBoundary b₁ b₂ x₁ x₂))
    (hB₁ : ∀ t ∈ Icc a b, δ t ∉ b₁ '' Ioo 0 1)
    (hB₂ : ∀ t ∈ Icc a b, δ t ∉ b₂ '' Ioo 0 1)
    (h0 : ∀ t ∈ Icc a b, δ t ≠ 0)
    (hR : ∀ c d, a ≤ c → c < d → d ≤ b → ∃ t ∈ Icc c d, δ t ∈ H)
    (ha : δ a = x₁ ∨ δ a = x₂ ∨ δ a ∈ closure (innerSide (compactBoundary b₁ b₂ x₁ x₂)))
    (hb : δ b ∈ closure (innerSide (compactBoundary b₁ b₂ x₁ x₂))) : δ a = δ b := by
  have hinter := fun {w : ℂ} (hw₁ : w ∈ b₁ '' Icc 0 1) (hw₂ : w ∈ b₂ '' Icc 0 1) =>
    psiArms_inter hz₁ hz₂ ho₁ ho₂ hH₁ hH₂ hdisj hw₁ hw₂
  rcases lt_trichotomy x₁ x₂ with hlt | heq | hlt
  · have h : IsArcPairInf x₁ x₂ b₁ b₂ :=
      ⟨hlt, hx₂, hc₁, hc₂, hi₁, hi₂, hz₁, hz₂, ho₁, ho₂, hH₁, hH₂, ?_⟩
    · simp only [compactBoundary, min_eq_left hlt.le, max_eq_right hlt.le] at hF ha hb
      exact (h.gate_lemma hab hδ hδH hF hB₁ hB₂ h0 hR ha hb).1
    · rintro w ⟨hw₁, hw₂⟩
      rcases hinter hw₁ hw₂ with hw | ⟨h1, h2⟩
      · exact hw
      · exact False.elim (hlt.ne (ofReal_injective (h1.symm.trans h2)))
  · subst x₂
    obtain ⟨hJ, -⟩ := compactBoundary_jordan hx₁ hx₂ hc₁ hc₂ hi₁ hi₂ hz₁ hz₂ ho₁ ho₂ hH₁ hH₂ hdisj
    have hend : ∀ t ∈ Icc a b, δ t ∈ closure (innerSide (compactBoundary b₁ b₂ x₁ x₁)) →
        δ t = x₁ := by
      intro t ht hcl
      have hm := mem_of_mem_closure_innerSide (isCompact_of_isJordanCurve hJ).isClosed hcl (hF t ht)
      have harm : ∀ {β : ℝ → ℂ}, β 0 = (x₁ : ℂ) → β 1 = 0 →
          δ t ∉ β '' Ioo 0 1 → δ t ∈ β '' Icc 0 1 → δ t = x₁ := by
        intro β hz ho hn hm
        rcases mem_arc_trichotomy hm with he | he | he
        · exact he.trans hz
        · exact False.elim (hn he)
        · exact False.elim (h0 t ht (he.trans ho))
      rcases hm with (hm | hm) | ⟨y, hy, he⟩
      · exact harm hz₁ ho₁ (hB₁ t ht) hm
      · exact harm hz₂ ho₂ (hB₂ t ht) hm
      · have hy' : y ∈ Icc x₁ x₁ := by simpa only [min_self, max_self] using hy
        have hyx : y = x₁ := le_antisymm hy'.2 hy'.1
        exact he.symm.trans (congrArg ofReal hyx)
    have hae : δ a = x₁ := by
      rcases ha with ha | ha | ha
      · exact ha
      · exact ha
      · exact hend a ⟨le_rfl, hab.le⟩ ha
    exact hae.trans (hend b ⟨hab.le, le_rfl⟩ hb).symm
  · have h : IsArcPairInf x₂ x₁ b₂ b₁ :=
      ⟨hlt, hx₁, hc₂, hc₁, hi₂, hi₁, hz₂, hz₁, ho₂, ho₁, hH₂, hH₁, ?_⟩
    · simp only [compactBoundary, min_eq_right hlt.le, max_eq_left hlt.le,
        union_comm (b₁ '' Icc 0 1) (b₂ '' Icc 0 1)] at hF ha hb
      have ha' : δ a = x₂ ∨ δ a = x₁ ∨ δ a ∈ closure
          (innerSide (b₂ '' Icc 0 1 ∪ b₁ '' Icc 0 1 ∪ ofReal '' Icc x₂ x₁)) := by
        rcases ha with ha | ha | ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inl ha
        · exact Or.inr (Or.inr ha)
      exact (h.gate_lemma hab hδ hδH hF hB₂ hB₁ h0 hR ha' hb).1
    · rintro w ⟨hw₂, hw₁⟩
      rcases hinter hw₁ hw₂ with hw | ⟨h1, h2⟩
      · exact hw
      · exact False.elim (hlt.ne (ofReal_injective (h2.symm.trans h1)))

end InteractingSLE.Sec7.R7InfinityGap
