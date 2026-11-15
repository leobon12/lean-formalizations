/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GVanDense

/-! # Measurability of vanishing on an open real boundary window

Closed intervals with rational endpoints cover every open real window.
Their complex images are compact, so the compact-patch criterion makes
the simultaneous boundary assertion measurable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology

namespace InteractingSLE.Sec5.Aux61GVan

/-- Rational closed intervals contained in an open set cover it. -/
theorem exists_rat_Icc_subset {O : Set ℝ} (hO : IsOpen O) {a : ℝ} (ha : a ∈ O) :
    ∃ p q : ℚ, a ∈ Icc (p : ℝ) q ∧ Icc (p : ℝ) q ⊆ O := by
  obtain ⟨l, u, hla, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hO.mem_nhds ha)
  obtain ⟨p, hlp, hpa⟩ := exists_rat_btwn hla.1
  obtain ⟨q, haq, hqu⟩ := exists_rat_btwn hla.2
  exact ⟨p, q, ⟨hpa.le, haq.le⟩, fun z hz => hsub ⟨hlp.trans_le hz.1, hz.2.trans_lt hqu⟩⟩

/-- The all-points boundary condition is a countable collection of
compact-patch boundary conditions. -/
theorem boundary_zero_iff_rat_patches {O : Set ℝ} (hO : IsOpen O)
    {U : Set ℂ} {f : ℂ → ℝ} :
    (∀ a ∈ O, Tendsto f (𝓝[U] (a : ℂ)) (𝓝 0)) ↔
      ∀ p q : ℚ, Icc (p : ℝ) q ⊆ O →
        ∀ z ∈ Complex.ofReal '' Icc (p : ℝ) q, Tendsto f (𝓝[U] z) (𝓝 0) := by
  constructor
  · rintro h p q hpq z ⟨a, ha, rfl⟩
    exact h a (hpq ha)
  · intro h a ha
    obtain ⟨p, q, hapq, hpq⟩ := exists_rat_Icc_subset hO ha
    exact h p q hpq _ ⟨a, hapq, rfl⟩

/-- Simultaneous zero boundary limits on any open real window form a
measurable event for an interior-continuous, pointwise measurable family. -/
theorem measurableSet_boundary_zero {β : Type*} [MeasurableSpace β]
    {U : Set ℂ} (hU : U.Nonempty) {O : Set ℝ} (hO : IsOpen O) {F : β → ℂ → ℝ}
    (hF : ∀ z ∈ U, Measurable (fun b => F b z)) (hc : ∀ b, ContinuousOn (F b) U) :
    MeasurableSet {b | ∀ a ∈ O, Tendsto (F b) (𝓝[U] (a : ℂ)) (𝓝 0)} := by
  have hm : MeasurableSet (⋂ p : ℚ, ⋂ q : ℚ, ⋂ (_ : Icc (p : ℝ) q ⊆ O),
      {b | ∀ z ∈ Complex.ofReal '' Icc (p : ℝ) q, Tendsto (F b) (𝓝[U] z) (𝓝 0)}) := by
    refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_tendsto_zero_on_compact hU
      (isCompact_Icc.image Complex.continuous_ofReal) hF hc
  convert hm using 1
  ext b
  simp only [mem_ofPred_eq, mem_iInter]
  exact boundary_zero_iff_rat_patches hO

end InteractingSLE.Sec5.Aux61GVan
