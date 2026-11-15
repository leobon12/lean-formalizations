/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerFace
import InteractingSLE.Spec.Sec7.R7GapEqGeoLoewner

/-!
# Target-face reduction to boundary geometry and forbidden bulges

PROVE-R7-GAPEQ. The named input below concerns ordinary planar boundary geometry. The
component image, target adherence, conformal relative chart and active confinement follow.
Germ comparisons are separate attachment inputs, as in the previous continuation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6 R7StopIn

/-- **Remaining selected-face geometry.** One Jordan curve in the current chart, an interior
witness in the pocket, an access landing at its target, and exclusion of the other pocket
preimages by forbidden bulges. No component image or prime-end equality is assumed. -/
def HasTargetFace (W : ℝ → ℝ) (C B : Set ℂ) (x : ℂ) (r : ℝ) : Prop :=
  ∃ (Γ : Set ℂ) (p z : ℂ), LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧
    p ∈ innerSide Γ ∧ trMap W 0 r p ∈ C ∧
    (∀ w ∈ innerSide Γ, trMap W 0 r w ∉ frontier C) ∧
    (∀ w ∈ Γ, w ∈ H → trMap W 0 r w ∉ C) ∧
    z ∈ Γ ∧ z ∈ H ∧ trMap W 0 r z = x ∧
    ∀ w ∈ H, trMap W 0 r w ∈ C → w ∉ innerSide Γ → trMap W 0 r w ∈ B

/-- The previous target-component and confinement input follows from `HasTargetFace` and
trace avoidance of its forbidden bulges. -/
theorem target_component_of_face_boundaries {W : ℝ → ℝ} {η : ℝ → ℂ}
    {C B : Set ℂ} {x : ℂ} {r : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hC : IsOpen C) (havoid : ∀ t, r ≤ t → η t ∉ B) (hface : HasTargetFace W C B x r) :
    ∃ (Γ : Set ℂ) (p q : ℂ), LQGMetric.JordanMap.IsJordanCurve Γ ∧ p ∈ Γᶜ ∧
      IsBounded (connectedComponentIn Γᶜ p) ∧ connectedComponentIn Γᶜ p ⊆ H ∧
      trMap W 0 r '' connectedComponentIn Γᶜ p =
        connectedComponentIn (C ∩ (H \ fwdHull W r)) q ∧
      x ∈ closure (trMap W 0 r '' connectedComponentIn Γᶜ p) ∧
      ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H →
        trMap W r t 0 ∈ connectedComponentIn Γᶜ p := by
  obtain ⟨Γ, p, z, hΓ, hΓH, hp, hpC, hfr, hbd, hz, hzH, hzx, hbulge⟩ := hface
  obtain ⟨⟨q, hq, hEq⟩, hFb, -, -, -, -, -, -, -⟩ := jordan_sides hΓ hΓH
  obtain ⟨-, himage⟩ := image_innerSide_eq_component hη hW hW0 hr hC hΓ hΓH hfr hbd hp hpC
  refine ⟨Γ, q, trMap W 0 r p, hΓ, hq, hEq ▸ hFb,
    hEq ▸ innerSide_subset_H hΓ hΓH, ?_, ?_, ?_⟩
  · rwa [← hEq]
  · rw [← hEq]
    exact target_mem_closure_face_image hη hW hW0 hr hΓ hΓH hz hzH hzx
  · rw [← hEq]
    exact ownFuture_mem_face_of_forbidden_bulges hη hW hW0 hr havoid hbulge

/-- **Relative Loewner evolution with only boundary geometry left.** The chart, component
identity, adherence and confinement premises of the landed reduction are all discharged.
The mapped gap input is stated separately so an old-access gate theorem can supply it. -/
theorem relLoewner_of_face_boundaries {W : ℝ → ℝ} {η : ℝ → ℂ} {C B : Set ℂ}
    {x y : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}
    (hP : IsErasurePocket η C x y τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hCH : C ⊆ H) (hψ : IsJordanCoord C x y ψ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hmapped : ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | s < t ∧ η t ∈ C} → b ∈ closure {t | a < t ∧ η t ∈ C} →
      trMap W s a 0 = trMap W s b 0)
    (hgeometry : ∀ u ∈ Ico (0 : ℝ) (pocketClock η C τ σ σ),
      HasTargetFace W C B x (pocketFibre η C τ σ u)) :
    RelLoewner (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) := by
  apply R7GapEqGeo.relLoewner_of_target_faces hP hη hW hW0 hCH hψ hmapped
  intro u hu
  have hs0 := hP.nonneg.trans (hP.fibre_mem u).1
  exact target_component_of_face_boundaries hη hW hW0 hs0 hP.isOpen
    (fun t ht => havoid t (hs0.trans ht)) (hgeometry u hu)

end InteractingSLE.Sec7.R7GapEqCorner
