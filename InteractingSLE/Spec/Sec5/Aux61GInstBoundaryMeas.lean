/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstCollarPieces

/-! # Measurability of distances to the old boundary in the bounded model -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GInst

/-- Distance to the compact range of a random continuous map is measurable.
The existing dense-sequence and extended-distance APIs reduce it to a
countable infimum. -/
theorem measurable_infDist_compact_range {X J : Type*} [MeasurableSpace X]
    [TopologicalSpace J] [CompactSpace J] [SecondCountableTopology J] [Nonempty J]
    {f : X → J → ℂ} (hfc : ∀ x, Continuous (f x))
    (hfm : ∀ j, Measurable (fun x => f x j)) (z : ℂ) :
    Measurable (fun x => infDist z (range (f x))) := by
  let e : ℕ → J := TopologicalSpace.denseSeq J
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq J
  have hcl : ∀ x, closure (range (fun n => f x (e n))) = range (f x) := by
    intro x
    apply Subset.antisymm
    · exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact mem_range_self _)
        (isCompact_range (hfc x)).isClosed
    · simpa only [← range_comp, Function.comp_def] using
        (hfc x).range_subset_closure_image_dense he
  have heq : (fun x => infDist z (range (f x))) =
      fun x => (⨅ n : ℕ, edist z (f x (e n))).toReal := by
    funext x
    rw [← hcl x, infDist_closure]
    unfold infDist infEDist
    congr 1
    simp only [mem_range, iInf_exists]
    rw [iInf_comm]
    simp
  rw [heq]
  exact ENNReal.measurable_toReal.comp (Measurable.iInf fun n => measurable_const.edist (hfm (e n)))

/-- The old boundary is the union of the circle and the bounded image of a
continuous counterflow record. Its distance is measurable from that record. -/
theorem measurable_infDist_oldModelBoundary {X : Type*} [MeasurableSpace X]
    {β : X → ℝ → ℂ} {s : ℝ} (hβc : ∀ x, ContinuousOn (β x) (Icc 0 s))
    (hβm : ∀ t, Measurable (fun x => β x t)) (z : ℂ) :
    Measurable (fun x => infDist z (oldModelBoundary (counterflowRecord (β x) s))) := by
  let J := (sphere (0 : ℂ) 1) ⊕ (Icc (0 : ℝ) s)
  haveI : CompactSpace (sphere (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  haveI : CompactSpace (Icc (0 : ℝ) s) := isCompact_iff_compactSpace.1 isCompact_Icc
  haveI : Nonempty (sphere (0 : ℂ) 1) := ⟨⟨1, by simp⟩⟩
  let f : X → J → ℂ := fun x => Sum.elim (fun a => a.1) (fun t => -cayley (clipH (β x t)))
  have hfc : ∀ x, Continuous (f x) := by
    intro x
    apply continuous_sum_dom.2
    refine ⟨continuous_subtype_val, ?_⟩
    exact ((continuousOn_cayley_Hbar.comp_continuous
      (continuous_clipH.comp ((hβc x).comp_continuous continuous_subtype_val (fun t => t.2)))
        (fun _ => clipH_mem_Hbar _)).neg)
  have hfm : ∀ j, Measurable (fun x => f x j) := by
    intro j
    cases j with
    | inl a => exact measurable_const
    | inr t =>
      have hm : Measurable cayley :=
        (measurable_id.sub measurable_const).div (measurable_id.add measurable_const)
      exact (hm.comp (continuous_clipH.measurable.comp (hβm t))).neg
  have he : ∀ x, range (f x) = oldModelBoundary (counterflowRecord (β x) s) := by
    intro x
    ext w
    constructor
    · rintro ⟨a | t, rfl⟩
      · exact Or.inl a.2
      · exact Or.inr ⟨clipH (β x t), ⟨t, t.2, rfl⟩, rfl⟩
    · rintro (hw | ⟨k, ⟨t, ht, rfl⟩, rfl⟩)
      · exact ⟨Sum.inl ⟨w, hw⟩, rfl⟩
      · exact ⟨Sum.inr ⟨t, ht⟩, rfl⟩
  simpa only [he] using measurable_infDist_compact_range hfc hfm z

end InteractingSLE.Sec5.Aux61GInst
