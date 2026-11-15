/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Counterflow

/-!
# Proposition 5.9: the inclusion of the light cone in the counterflow range (from Lemma 5.7)

Packet PROVE-SEC5-D. Specification p. 141 (proof of Proposition 5.9): "Lemma 5.7, applied to the countably many allowed
finite lists, gives the inclusion of this closed accessible set in the indicated counterflow range. We prove the reverse
inclusion by constructing allowed trajectories". The closures are "Euclidean closures in the closure of the original
strip, and include limiting marked endpoints" — in the chart `E` the closure in `ℂ`.

* `closure_iUnion_subset_image_Icc`: a union of sets contained in the range `ξ([0, 1])` of a path continuous on `[0, 1]`
  (the completed counterflow, `Sec4.stripCounterflowPath`) has its closure in that range (the range is compact);
* `ae_closure_iUnion_subset_stripCounterflowPath`: almost surely, for a countable family of explored paths each
  almost surely contained in the completed counterflow range (Lemma 5.7 for each allowed finite list, e.g. the output of
  `Sec4.lemma47_of_remark48_strip`), the closed accessible set `closure (⋃ₖ ηₖ([0, Tₖ]))` lies in the completed range.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

/-- The closure of a union of subsets of the range `ξ([0, 1])` of a path continuous on `[0, 1]` lies in that range. -/
theorem closure_iUnion_subset_image_Icc {ξ : ℝ → ℂ} (hξ : ContinuousOn ξ (Icc 0 1)) {ι : Type*}
    {S : ι → Set ℂ} (hS : ∀ i, S i ⊆ ξ '' Icc 0 1) : closure (⋃ i, S i) ⊆ ξ '' Icc 0 1 :=
  closure_minimal (iUnion_subset hS) (isCompact_Icc.image_of_continuousOn hξ).isClosed

/-- **The light-cone inclusion of Proposition 5.9 from Lemma 5.7.** Let `γ ω` be the counterflow trace in the chart
`M_q` (continuous, avoiding `−1`, tending to `∞`: the inputs of `Sec4.continuousOn_stripCounterflowPath`), and
`(ηₖ, Tₖ)` a countable family of explored paths (the allowed angle-varying flow lines with their stopping times), each
almost surely contained, on `[0, Tₖ]`, in the completed counterflow range (Lemma 5.7). Then almost surely the closed
accessible set `closure (⋃ₖ ηₖ([0, Tₖ]))` lies in the completed counterflow range `ξ([0, 1])`. -/
theorem ae_closure_iUnion_subset_stripCounterflowPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {q : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {ι : Type*} [Countable ι] {η : ι → Ω → ℝ → ℂ} {T : ι → Ω → ℝ}
    (hγ : ∀ᵐ ω ∂P, Continuous (γ ω) ∧ (∀ t, γ ω t ≠ -1) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (h57 : ∀ k, ∀ᵐ ω ∂P, η k ω '' Icc 0 (T k ω) ⊆ Sec4.stripCounterflowPath q (γ ω) '' Icc 0 1) :
    ∀ᵐ ω ∂P, closure (⋃ k, η k ω '' Icc 0 (T k ω)) ⊆ Sec4.stripCounterflowPath q (γ ω) '' Icc 0 1 := by
  filter_upwards [hγ, ae_all_iff.2 h57] with ω ⟨hc, hne, hinf⟩ hω
  exact closure_iUnion_subset_image_Icc (Sec4.continuousOn_stripCounterflowPath hc hne hinf) hω

end Sec5

end InteractingSLE
