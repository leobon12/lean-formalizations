/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD12Upper

/-!
# Constructing the capacity extension from a joined chart path

Packet PROVE-T14-GW2ROOT2. Compactness, attachment, boundedness and both
filling identities in C11's extension predicate are proved here. Only
the literal carrier identities, old chart and attaching seed are inputs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD12

open Restart

/-- Joining a continuous relative path to an attached compact carrier
constructs every field of the earlier capacity-extension predicate. -/
theorem isCapacityExtension_of_upper_parts {A B K : Set ℂ} {g φ ψ : ℂ → ℂ}
    {x₀ : ℂ} {Γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hA : A = K ∩ H) (hK : IsCompact K)
    (hcK : IsPreconnected (K ∪ {z : ℂ | z.im ≤ 0}))
    (hD : Supp7.IsDomChart K φ ψ) (hg : IsMapOut (fillH K) g)
    (hφ : ∀ z, φ z = g z - x₀) (hx₀ : x₀.im = 0)
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓH : MapsTo Γ (Icc 0 t) Hbar)
    (hseed : ψ (Γ 0) ∈ K)
    (hB : B = (K ∪ ψ '' (Γ '' Icc 0 t)) ∩ H) :
    RootC11.IsCapacityExtension A B K (K ∪ ψ '' (Γ '' Icc 0 t))
      g φ ψ x₀ Γ t := by
  have hψΓc : ContinuousOn (ψ ∘ Γ) (Icc 0 t) := hD.continuousOn_inv.comp hΓc hΓH
  have hJ : IsCompact (ψ '' (Γ '' Icc 0 t)) := by
    rw [image_image]
    exact isCompact_Icc.image_of_continuousOn hψΓc
  have hcJ : IsPreconnected (ψ '' (Γ '' Icc 0 t)) := by
    rw [image_image]
    exact isPreconnected_Icc.image _ hψΓc
  have hcP : IsPreconnected
      ((K ∪ ψ '' (Γ '' Icc 0 t)) ∪ {z : ℂ | z.im ≤ 0}) := by
    have hmem : ψ (Γ 0) ∈ ψ '' (Γ '' Icc 0 t) :=
      ⟨Γ 0, ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩, rfl⟩
    have h := hcK.union (ψ (Γ 0)) (Or.inl hseed) hmem hcJ
    rwa [union_right_comm] at h
  have hP := hK.union hJ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hP, hD, hg, hφ, hx₀, subset_rfl, ?_⟩
  · rw [hA]
    exact hK.isBounded.subset inter_subset_left
  · rw [hA]
    exact isPreconnected_inter_H_union_lowerHalf hcK
  · rw [hB]
    exact hP.isBounded.subset inter_subset_left
  · rw [hB]
    exact isPreconnected_inter_H_union_lowerHalf hcP
  · rw [hA]
    exact Sec7.SideHeight.fillH_inter_H _
  · rw [hB]
    exact Sec7.SideHeight.fillH_inter_H _
  · intro r hr
    exact Or.inr ⟨Γ r, ⟨r, hr, rfl⟩, rfl⟩

/-- Specialization to an old continuous prefix. No separate compactness,
boundedness, attachment or filling hypotheses are needed. -/
theorem isCapacityExtension_of_upper_prefix {A B : Set ℂ} {γ Γ : ℝ≥0 → ℂ}
    {v t : ℝ≥0} {g φ ψ : ℂ → ℂ} {x₀ : ℂ}
    (hA : A = γ '' Icc 0 v ∩ H) (hc : ContinuousOn γ (Icc 0 v))
    (h0 : (γ 0).im ≤ 0) (hD : Supp7.IsDomChart (γ '' Icc 0 v) φ ψ)
    (hg : IsMapOut (fillH (γ '' Icc 0 v)) g)
    (hφ : ∀ z, φ z = g z - x₀) (hx₀ : x₀.im = 0)
    (hΓc : ContinuousOn Γ (Icc 0 t)) (hΓH : MapsTo Γ (Icc 0 t) Hbar)
    (hseed : ψ (Γ 0) ∈ γ '' Icc 0 v)
    (hB : B = (γ '' Icc 0 v ∪ ψ '' (Γ '' Icc 0 t)) ∩ H) :
    RootC11.IsCapacityExtension A B (γ '' Icc 0 v)
      (γ '' Icc 0 v ∪ ψ '' (Γ '' Icc 0 t)) g φ ψ x₀ Γ t :=
  isCapacityExtension_of_upper_parts hA (isCompact_Icc.image_of_continuousOn hc)
    (isPreconnected_image_union_lowerHalf hc h0) hD hg hφ hx₀ hΓc hΓH hseed hB

end InteractingSLE.Theorem14.GW2TipSystem.RootD12
