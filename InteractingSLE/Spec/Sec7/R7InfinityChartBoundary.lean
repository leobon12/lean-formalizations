/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityChartArms

/-!
# The compactified two-arm Jordan boundary

PROVE-R7-GAPEQ. The real interval between the two compact gates is allowed to
degenerate. Its half-plane boundary points map to the original pocket frontier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6 PocketJordan

/-- The two compactified incoming arms, joined by the real segment between gates. -/
def compactBoundary (b₁ b₂ : ℝ → ℂ) (x₁ x₂ : ℝ) : Set ℂ :=
  b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 ∪ ofReal '' Icc (min x₁ x₂) (max x₁ x₂)

/-- Two disjoint open arms give a Jordan boundary even when their gates coincide. -/
theorem compactBoundary_jordan {b₁ b₂ : ℝ → ℂ} {x₁ x₂ : ℝ}
    (hx₁ : x₁ < 0) (hx₂ : x₂ < 0)
    (hc₁ : ContinuousOn b₁ (Icc 0 1)) (hc₂ : ContinuousOn b₂ (Icc 0 1))
    (hi₁ : InjOn b₁ (Icc 0 1)) (hi₂ : InjOn b₂ (Icc 0 1))
    (hz₁ : b₁ 0 = x₁) (hz₂ : b₂ 0 = x₂) (ho₁ : b₁ 1 = 0) (ho₂ : b₂ 1 = 0)
    (hH₁ : ∀ v ∈ Ioo (0 : ℝ) 1, b₁ v ∈ H) (hH₂ : ∀ v ∈ Ioo (0 : ℝ) 1, b₂ v ∈ H)
    (hdisj : ∀ w ∈ b₁ '' Ioo 0 1, w ∉ b₂ '' Ioo 0 1) :
    LQGMetric.JordanMap.IsJordanCurve (compactBoundary b₁ b₂ x₁ x₂) ∧
      compactBoundary b₁ b₂ x₁ x₂ ⊆ Hbar := by
  have hinter := fun {w : ℂ} (hw₁ : w ∈ b₁ '' Icc 0 1) (hw₂ : w ∈ b₂ '' Icc 0 1) =>
    psiArms_inter hz₁ hz₂ ho₁ ho₂ hH₁ hH₂ hdisj hw₁ hw₂
  rcases lt_trichotomy x₁ x₂ with hlt | heq | hlt
  · have hpair : IsArcPairInf x₁ x₂ b₁ b₂ :=
      ⟨hlt, hx₂, hc₁, hc₂, hi₁, hi₂, hz₁, hz₂, ho₁, ho₂, hH₁, hH₂, ?_⟩
    · simpa only [compactBoundary, min_eq_left hlt.le, max_eq_right hlt.le] using hpair.isJordanCurve_face
    · rintro w ⟨hw₁, hw₂⟩
      rcases hinter hw₁ hw₂ with hw | ⟨h1, h2⟩
      · exact hw
      · exact False.elim (hlt.ne (ofReal_injective (h1.symm.trans h2)))
  · subst x₂
    have hJ := Sec7.isJordanCurve_image_union hc₁ hc₂ hi₁ hi₂ (hz₁.trans hz₂.symm)
      (ho₁.trans ho₂.symm) (fun w hw => by
        rcases hinter hw.1 hw.2 with h0 | ⟨h1, -⟩
        · exact Or.inr (h0.trans ho₁.symm)
        · exact Or.inl (h1.trans hz₁.symm))
    have hg : (x₁ : ℂ) ∈ b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 :=
      Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hz₁⟩
    have hb : compactBoundary b₁ b₂ x₁ x₁ = b₁ '' Icc 0 1 ∪ b₂ '' Icc 0 1 := by
      rw [compactBoundary, min_self, max_self, Icc_self, image_singleton,
        union_eq_left.2 (singleton_subset_iff.2 hg)]
    rw [hb]
    exact ⟨hJ, union_subset (image_arcInf_subset_Hbar hz₁ ho₁ hH₁)
      (image_arcInf_subset_Hbar hz₂ ho₂ hH₂)⟩
  · have hpair : IsArcPairInf x₂ x₁ b₂ b₁ :=
      ⟨hlt, hx₁, hc₂, hc₁, hi₂, hi₁, hz₂, hz₁, ho₂, ho₁, hH₂, hH₁, ?_⟩
    · simpa only [compactBoundary, min_eq_right hlt.le, max_eq_left hlt.le,
        union_comm (b₁ '' Icc 0 1) (b₂ '' Icc 0 1)] using hpair.isJordanCurve_face
    · rintro w ⟨hw₂, hw₁⟩
      rcases hinter hw₁ hw₂ with hw | ⟨h1, h2⟩
      · exact hw
      · exact False.elim (hlt.ne (ofReal_injective (h2.symm.trans h1)))

/-- The common original target belongs to the compact boundary. -/
theorem zero_mem_compactBoundary {b₁ b₂ : ℝ → ℂ} {x₁ x₂ : ℝ} (ho₁ : b₁ 1 = 0) :
    (0 : ℂ) ∈ compactBoundary b₁ b₂ x₁ x₂ :=
  Or.inl (Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, ho₁⟩)

/-- Only the open compactified arms contribute half-plane boundary points. -/
theorem mem_open_arms_of_mem_compactBoundary {b₁ b₂ : ℝ → ℂ} {x₁ x₂ : ℝ}
    (hz₁ : b₁ 0 = x₁) (hz₂ : b₂ 0 = x₂) (ho₁ : b₁ 1 = 0) (ho₂ : b₂ 1 = 0)
    {w : ℂ} (hw : w ∈ compactBoundary b₁ b₂ x₁ x₂) (hwH : w ∈ H) :
    w ∈ b₁ '' Ioo 0 1 ∪ b₂ '' Ioo 0 1 := by
  have harm : ∀ {b : ℝ → ℂ} {x : ℝ}, b 0 = x → b 1 = 0 → w ∈ b '' Icc 0 1 →
      w ∈ b '' Ioo 0 1 := by
    intro b x hz ho hb
    rcases mem_arc_trichotomy hb with h0 | hI | h1
    · exact False.elim (not_mem_H_ofReal x ((h0.trans hz) ▸ hwH))
    · exact hI
    · exact False.elim (not_mem_H_ofReal 0 (by simpa only [ofReal_zero] using (h1.trans ho) ▸ hwH))
  rcases hw with (hw | hw) | ⟨x, -, rfl⟩
  · exact Or.inl (harm hz₁ ho₁ hw)
  · exact Or.inr (harm hz₂ ho₂ hw)
  · exact False.elim (not_mem_H_ofReal x hwH)

end InteractingSLE.Sec7.R7InfinityChart
