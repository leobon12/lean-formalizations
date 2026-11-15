/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GVanPatches
import Mathlib.MeasureTheory.Measure.Map

/-! # Boundary cancellation passes to the retained-history law

The simultaneous boundary event is measurable by the rational compact-patch
criterion. Its almost-sure assertion can therefore be transported in both
directions by the ordinary image-measure theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology

namespace InteractingSLE.Sec5.Aux61GVan

/-- Almost-sure vanishing on an open real window, localized to a measurable
history event, is equivalent under the history law and its original law. -/
theorem ae_boundary_zero_map_iff {X β : Type*} [MeasurableSpace X] [MeasurableSpace β]
    {μ : Measure X} {Z : X → β} (hZ : Measurable Z) {B : Set β} (hB : MeasurableSet B)
    {U : Set ℂ} (hU : U.Nonempty) {O : Set ℝ} (hO : IsOpen O) {F : β → ℂ → ℝ}
    (hF : ∀ z ∈ U, Measurable (fun b => F b z)) (hc : ∀ b, ContinuousOn (F b) U) :
    (∀ᵐ b ∂μ.map Z, b ∈ B → ∀ a ∈ O, Tendsto (F b) (𝓝[U] (a : ℂ)) (𝓝 0)) ↔
      ∀ᵐ x ∂μ, Z x ∈ B → ∀ a ∈ O, Tendsto (F (Z x)) (𝓝[U] (a : ℂ)) (𝓝 0) := by
  have he : {b | b ∈ B → ∀ a ∈ O, Tendsto (F b) (𝓝[U] (a : ℂ)) (𝓝 0)} =
      Bᶜ ∪ {b | ∀ a ∈ O, Tendsto (F b) (𝓝[U] (a : ℂ)) (𝓝 0)} := by
    ext b
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  have hm : MeasurableSet {b | b ∈ B → ∀ a ∈ O, Tendsto (F b) (𝓝[U] (a : ℂ)) (𝓝 0)} := by
    rw [he]
    exact hB.compl.union (measurableSet_boundary_zero hU hO hF hc)
  exact ae_map_iff hZ.aemeasurable hm

end InteractingSLE.Sec5.Aux61GVan
