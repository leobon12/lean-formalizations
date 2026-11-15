/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerFace

/-!
# The central face with surviving outer tails

PROVE-R6-TWO, Astra §2.3 (R98). An outer wall after its first contact
need not be swallowed. Only its active image must avoid the central
face. The component theorem is reused from `R7GapEqCornerFace`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R6Ts

open Sec6

/-- The exact outer-tail condition needed for the central face. It
allows arbitrary surviving tail components on the other side. -/
def OuterTailExclusion (W : ℝ → ℝ) (t : ℝ) (Γ : Set ℂ)
    (α : ℝ → ℂ) (u e : ℝ) : Prop :=
  ∀ v ∈ Icc u e, α v ∈ H \ fwdHull W t → fwdMap W t (α v) ∉ innerSide Γ

/-- Aux. 31's closed exterior-side conclusion is enough. Active tail
points on the Jordan boundary itself are also permitted. -/
theorem outerTailExclusion_of_closed_exterior
    {W : ℝ → ℝ} {t : ℝ} {Γ : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    {α : ℝ → ℂ} {u e : ℝ}
    (hside : ∀ v ∈ Icc u e, α v ∈ H \ fwdHull W t →
      fwdMap W t (α v) ∈ closure (outerSide Γ)) :
    OuterTailExclusion W t Γ α u e := by
  have hdisj := (disjoint_innerSide_outerSide (J := Γ)).closure_right
    (jordan_sides hΓ hΓH).2.2.2.2.1
  intro v hv hvD hw
  exact Set.disjoint_left.1 hdisj hw (hside v hv hvD)

/-- Incoming prefixes map to the proposed boundary, while active tail
points lie outside its inner side. Hence the entire pocket frontier
misses that inner side. No tail is assumed to be swallowed. -/
theorem innerSide_avoids_frontier_of_outer_tails
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {C Γ : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    {α₁ α₂ : ℝ → ℂ} {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ}
    (hfront : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (hprefix₁ : ∀ v ∈ Ico c₁ u₁, fwdMap W t (α₁ v) ∈ Γ)
    (hprefix₂ : ∀ v ∈ Ico c₂ u₂, fwdMap W t (α₂ v) ∈ Γ)
    (htail₁ : OuterTailExclusion W t Γ α₁ u₁ e₁)
    (htail₂ : OuterTailExclusion W t Γ α₂ u₂ e₂) :
    ∀ w ∈ innerSide Γ, trMap W 0 t w ∉ frontier C := by
  intro w hw hf
  have hwH := innerSide_subset_H hΓ hΓH hw
  have hwD := trMap_zero_mem_domain hW hW0 ht hwH
  have hinv := fwdMap_trMap_zero hW hW0 ht hwH
  have harms : ∀ (α : ℝ → ℂ) (c u e : ℝ),
      (∀ v ∈ Ico c u, fwdMap W t (α v) ∈ Γ) →
      OuterTailExclusion W t Γ α u e →
      trMap W 0 t w ∉ α '' Icc c e := by
    intro α c u e hp hs
    rintro ⟨v, hv, heq⟩
    have hvD : α v ∈ H \ fwdHull W t := heq ▸ hwD
    have hvw : fwdMap W t (α v) = w := by rw [heq]; exact hinv
    rcases lt_or_ge v u with hvu | huv
    · exact (innerSide_subset_compl hw) (hvw ▸ hp v ⟨hv.1, hvu⟩)
    · exact hs v ⟨huv, hv.2⟩ hvD (hvw.symm ▸ hw)
  rw [hfront] at hf
  exact hf.elim (harms α₁ c₁ u₁ e₁ hprefix₁ htail₁)
    (harms α₂ c₂ u₂ e₂ hprefix₂ htail₂)

/-- Boundary continuity gives adherence even at a real boundary point
of the ambient face. This includes the current driver. -/
theorem landing_mem_closure_face_image
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    {x : ℂ} (hx : x ∈ Γ) :
    trMap W 0 t x ∈ closure (trMap W 0 t '' innerSide Γ) := by
  have hfront := (jordan_sides hΓ hΓH).2.2.1
  have hxfr : x ∈ frontier (innerSide Γ) := by rw [hfront]; exact hx
  have hxcl : x ∈ closure (innerSide Γ) := frontier_subset_closure hxfr
  have hsub : innerSide Γ ⊆ Hbar :=
    (innerSide_subset_H hΓ hΓH).trans QuantumZipper.H_subset_Hbar
  exact ((YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl ht x
    (hΓH hx)).mono hsub).mem_closure_image hxcl

/-- A boundary landing in the open pocket supplies the interior witness
required by the existing component theorem. In particular this witness
need not be included in the geometric face input. -/
theorem image_innerSide_eq_component_of_landing
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {C Γ : Set ℂ} (hC : IsOpen C)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hfr : ∀ w ∈ innerSide Γ, trMap W 0 t w ∉ frontier C)
    (hbd : ∀ w ∈ Γ, w ∈ H → trMap W 0 t w ∈ frontier C)
    {x : ℂ} (hx : x ∈ Γ) (hxC : trMap W 0 t x ∈ C) :
    ∃ p ∈ innerSide Γ, MapsTo (trMap W 0 t) (innerSide Γ) C ∧
      trMap W 0 t '' innerSide Γ =
        connectedComponentIn (C ∩ (H \ fwdHull W t)) (trMap W 0 t p) := by
  have hcl := landing_mem_closure_face_image hη hW hW0 ht hΓ hΓH hx
  obtain ⟨z, hzC, p, hp, hpz⟩ := (_root_.mem_closure_iff.1 hcl) C hC hxC
  have hpC : trMap W 0 t p ∈ C := hpz ▸ hzC
  obtain ⟨hmap, himage⟩ := R7GapEqCorner.image_innerSide_eq_component
    hη hW hW0 ht hC hΓ hΓH hfr
    (fun w hw hwH => by
      have h := hbd w hw hwH
      rw [hC.frontier_eq] at h
      exact h.2) hp hpC
  exact ⟨p, hp, hmap, himage⟩

/-- The outer analogue of the contained-pocket face identification,
with exterior-tail exclusion replacing the swallowed-tail assumption.
The conclusion identifies one selected component, allowing surviving
outer bulges elsewhere. -/
theorem image_innerSide_eq_component_of_outer_tails
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {C Γ : Set ℂ} (hC : IsOpen C)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    {α₁ α₂ : ℝ → ℂ} {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ}
    (hfront : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (hprefix₁ : ∀ v ∈ Ico c₁ u₁, fwdMap W t (α₁ v) ∈ Γ)
    (hprefix₂ : ∀ v ∈ Ico c₂ u₂, fwdMap W t (α₂ v) ∈ Γ)
    (htail₁ : OuterTailExclusion W t Γ α₁ u₁ e₁)
    (htail₂ : OuterTailExclusion W t Γ α₂ u₂ e₂)
    (hbd : ∀ w ∈ Γ, w ∈ H → trMap W 0 t w ∈ frontier C)
    {x : ℂ} (hx : x ∈ Γ) (hxC : trMap W 0 t x ∈ C) :
    ∃ p ∈ innerSide Γ, MapsTo (trMap W 0 t) (innerSide Γ) C ∧
      trMap W 0 t '' innerSide Γ =
        connectedComponentIn (C ∩ (H \ fwdHull W t)) (trMap W 0 t p) :=
  image_innerSide_eq_component_of_landing hη hW hW0 ht hC hΓ hΓH
    (innerSide_avoids_frontier_of_outer_tails hW hW0 ht hΓ hΓH
      hfront hprefix₁ hprefix₂ htail₁ htail₂) hbd hx hxC

end InteractingSLE.Sec7.R6Ts
