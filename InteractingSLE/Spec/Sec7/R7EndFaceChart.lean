/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceMixed

/-!
# The precise remaining compactified-face chart input

PROVE-R7-GAPEQ. Physical end selection and future confinement are proved. This file
isolates the remaining Jordan chart identification and transports confinement through it.
It does not assert that the source mixed walls already supply that chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan

/-- Remaining compactified Jordan identification. The representative `q` selects the
unique unbounded physical component; the real pole is `a` and the end maps to zero. -/
def InfiniteFaceChart (W : ℝ → ℝ) (C : Set ℂ) (s a : ℝ) (Γ : Set ℂ) (q : ℂ) : Prop :=
  LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧ (0 : ℂ) ∈ Γ ∧
    q ∈ C ∩ (H \ fwdHull W s) ∧
    ¬ IsBounded (connectedComponentIn (C ∩ (H \ fwdHull W s)) q) ∧
    (fun ζ => trMap W 0 s (psiMapInv a ζ)) '' innerSide Γ =
      connectedComponentIn (C ∩ (H \ fwdHull W s)) q

/-- The named chart identification gives exactly the current lift of the selected
physical component, without a further image or inverse-map hypothesis. -/
theorem lift_eq_infinite_face {W : ℝ → ℝ} {C Γ : Set ℂ} {s a : ℝ} {q : ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hchart : InfiniteFaceChart W C s a Γ q) :
    fwdMap W s '' connectedComponentIn (C ∩ (H \ fwdHull W s)) q =
      psiMapInv a '' innerSide Γ := by
  rw [← hchart.2.2.2.2.2, image_image]
  exact image_congr fun ζ hζ => fwdMap_trMap_zero hW hW0 hs
    (psiMapInv_mem_H (innerSide_subset_H hchart.1 hchart.2.1 hζ))

/-- Source avoidance and physical component selection imply compactified active
confinement once the remaining chart identification is supplied. -/
theorem ownFuture_mem_infinite_face {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : ℝ → ℝ} {η : ℝ → ℂ} {F Γ : Set ℂ} {τ s a : ℝ} {q : ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hs : 0 ≤ s) (hτs : τ ≤ s)
    (hallowed : AllowedUnboundedComponents W (cfPocket R L r) F τ)
    (hchart : InfiniteFaceChart W (cfPocket R L r) s a Γ q)
    (havoid : ∀ t, s ≤ t → η t ∉ F) :
    ∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
      psiMap a (trMap W s t 0) ∈ innerSide Γ := by
  intro t hst htC htH
  have ht := ownFuture_mem_unbounded_component h h0 hη hW hW0 hs hτs hallowed
    hchart.2.2.2.2.1 havoid t hst htC htH
  rw [lift_eq_infinite_face hW hW0 hs hchart] at ht
  obtain ⟨ζ, hζ, hζt⟩ := ht
  rw [← hζt, psiMap_psiMapInv]
  exact hζ

/-- Visit limits stay in the compactified closed face at every point where the real
pole is avoided. No singleton prime-end claim at an old physical contact is used. -/
theorem ownFuture_mem_closure_infinite_face {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : ℝ → ℝ} {η : ℝ → ℂ} {F Γ : Set ℂ} {τ s a b : ℝ} {q : ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hs : 0 ≤ s) (hτs : τ ≤ s)
    (hallowed : AllowedUnboundedComponents W (cfPocket R L r) F τ)
    (hchart : InfiniteFaceChart W (cfPocket R L r) s a Γ q)
    (havoid : ∀ t, s ≤ t → η t ∉ F)
    (hb : b ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r})
    (hpole : trMap W s b 0 ≠ a) :
    psiMap a (trMap W s b 0) ∈ closure (innerSide Γ) := by
  have hbcl := ownFuture_mem_closure_unbounded_component h h0 hη hW hW0 hs hτs
    hallowed hchart.2.2.2.2.1 havoid hb
  rw [lift_eq_infinite_face hW hW0 hs hchart] at hbcl
  have hc : ContinuousAt (psiMap a) (trMap W s b 0) :=
    continuousOn_psiMap.continuousAt (isOpen_compl_singleton.mem_nhds hpole)
  have hm := hc.continuousWithinAt.mem_closure_image hbcl
  rw [image_image] at hm
  have heq : (fun ζ => psiMap a (psiMapInv a ζ)) = id := funext psiMap_psiMapInv
  rwa [heq, image_id] at hm

end InteractingSLE.Sec7.R7EndFace
