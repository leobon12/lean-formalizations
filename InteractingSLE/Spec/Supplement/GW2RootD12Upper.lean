/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC11Meas
import InteractingSLE.Spec.Sec7.SideHeightRange

/-!
# GW2 prefix geometry from the upper part of a continuous trace

Packet PROVE-T14-GW2ROOT2. Boundedness, attachment and a compact filling
representative follow from a literal trace representation. The statement
does not assert that representation for an actual root image.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD12

open Restart

/-- Removing points outside the upper half-plane does not change attachment
to the lower half-plane. -/
theorem inter_H_union_lowerHalf (K : Set ℂ) :
    K ∩ H ∪ {z : ℂ | z.im ≤ 0} = K ∪ {z : ℂ | z.im ≤ 0} := by
  ext z
  constructor
  · rintro (⟨hz, _⟩ | hz)
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · by_cases hzH : z ∈ H
      · exact Or.inl ⟨hz, hzH⟩
      · exact Or.inr (show z.im ≤ 0 from le_of_not_gt hzH)
    · exact Or.inr hz

/-- Attachment of a carrier passes to its literal upper part. -/
theorem isPreconnected_inter_H_union_lowerHalf {K : Set ℂ}
    (hK : IsPreconnected (K ∪ {z : ℂ | z.im ≤ 0})) :
    IsPreconnected (K ∩ H ∪ {z : ℂ | z.im ≤ 0}) := by
  rwa [inter_H_union_lowerHalf]

/-- A continuous prefix from the lower boundary supplies all geometric
conditions of `capOf`, and its full trace is a compact representative. -/
theorem upper_prefix_geometry {γ : ℝ≥0 → ℂ} {v : ℝ≥0}
    (hc : ContinuousOn γ (Icc 0 v)) (h0 : (γ 0).im ≤ 0) :
    IsCompact (γ '' Icc 0 v) ∧
      Bornology.IsBounded (γ '' Icc 0 v ∩ H) ∧
      IsPreconnected (γ '' Icc 0 v ∩ H ∪ {z : ℂ | z.im ≤ 0}) ∧
      fillH (γ '' Icc 0 v ∩ H) = fillH (γ '' Icc 0 v) := by
  have hK := isCompact_Icc.image_of_continuousOn hc
  exact ⟨hK, hK.isBounded.subset inter_subset_left,
    isPreconnected_inter_H_union_lowerHalf (isPreconnected_image_union_lowerHalf hc h0),
    Sec7.SideHeight.fillH_inter_H _⟩

/-- Removing the non-upper part of a continuous attached trace preserves
its literal half capacity, including a prefix of length zero. -/
theorem capOf_upper_prefix_eq {γ : ℝ≥0 → ℂ} {v : ℝ≥0}
    (hc : ContinuousOn γ (Icc 0 v)) (h0 : (γ 0).im ≤ 0) :
    capOf (γ '' Icc 0 v ∩ H) = capOf (γ '' Icc 0 v) := by
  obtain ⟨hK, hb, ha, hf⟩ := upper_prefix_geometry hc h0
  rw [RootC11.capOf_eq_hcapSet hb ha,
    RootC11.capOf_eq_hcapSet hK.isBounded (isPreconnected_image_union_lowerHalf hc h0), hf]

end InteractingSLE.Theorem14.GW2TipSystem.RootD12
