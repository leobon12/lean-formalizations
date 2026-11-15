/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibDataChart
import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-! # Measurable chart and capacity readers for arbitrary recorded prefixes -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open Aux61FibData Restart LawUnique

/-- A Borel extension of chart evaluation, obtained from finite-valued
approximations. At every interior point it is the actual forward chart. -/
def readChart (c : Chart) (z : ℂ) : ℂ :=
  limUnder atTop fun n : ℕ =>
    let a := SimpleFunc.approxOn id measurable_id univ 0 (mem_univ _) n z
    (c.dom : Set ℂ).indicator c.1 a

theorem measurable_readChart {X : Type*} [MeasurableSpace X]
    {c : X → Chart} (hc : IsMeasChart c) {z : X → ℂ} (hz : Measurable z) :
    Measurable fun x => readChart (c x) (z x) := by
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  let a := SimpleFunc.approxOn z hz univ 0 (mem_univ _) n
  let J := range a
  have : Countable J := a.finite_range.countable.to_subtype
  let N : X → J := fun x => ⟨a x, mem_range_self x⟩
  have hN : Measurable N := a.measurable.subtype_mk
  have hG : Measurable fun p : X × J =>
      {x | (p.2 : ℂ) ∈ (c x).dom}.indicator (fun x => (c x).1 p.2) p.1 :=
    measurable_from_prod_countable_left fun j => hc.fwd j
  exact (hG.comp (measurable_id.prodMk hN)).stronglyMeasurable

theorem readChart_eq {c : Chart} (hc : c.IsConformal) {z : ℂ} (hz : z ∈ c.dom) :
    readChart c z = c.1 z := by
  have ht : Tendsto (fun n : ℕ => SimpleFunc.approxOn id measurable_id univ 0 (mem_univ _) n z)
      atTop (𝓝 z) := SimpleFunc.tendsto_approxOn measurable_id (mem_univ _) (by simp)
  have he := ht.eventually (c.dom.isOpen.mem_nhds hz)
  apply Tendsto.limUnder_eq
  have hc' := hc.differentiableOn_fwd.continuousOn.continuousAt (c.dom.isOpen.mem_nhds hz)
  refine (hc'.tendsto.comp ht).congr' ?_
  filter_upwards [he] with n hn
  exact (indicator_of_mem hn _).symm

/-- The closure of a countable family of measurable points is hitting measurable. -/
theorem measurable_closure_range {X J : Type*} [MeasurableSpace X] [Countable J]
    {f : X → J → ℂ} (hf : ∀ j, Measurable fun x => f x j) :
    Measurable[_, hittingSigma] fun x => closure (range (f x)) := by
  refine @measurable_generateFrom X (Set ℂ) _ _ _ fun S hS => ?_
  obtain ⟨U, hU, -, rfl⟩ := hS
  have he : (fun x => closure (range (f x))) ⁻¹' {A | (A ∩ U).Nonempty} =
      ⋃ j, {x | f x j ∈ U} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, closure_inter_open_nonempty_iff hU]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, hj⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨_, mem_range_self j, hj⟩
  rw [he]
  exact MeasurableSet.iUnion fun j => hf j hU.measurableSet

/-- On a continuous finite prefix, closing the sampled dyadic range gives
exactly the compact trace prefix, including its terminal point. -/
theorem closure_range_clamped_dyadic {γ : ℝ≥0 → ℂ} {v : ℝ≥0}
    (hc : ContinuousOn γ (Icc 0 v)) :
    closure (range fun p : ℕ × ℕ => γ (min (dyadicTime p) v)) = γ '' Icc 0 v := by
  apply Subset.antisymm
  · apply closure_minimal
    · rintro _ ⟨p, rfl⟩
      exact ⟨_, ⟨zero_le, min_le_right _ _⟩, rfl⟩
    · exact (isCompact_Icc.image_of_continuousOn hc).isClosed
  · rintro _ ⟨u, hu, rfl⟩
    have ht : Tendsto (fun n => dyadicTime (lowerDyadic u n)) atTop (𝓝[Icc 0 v] u) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicTime_lowerDyadic u,
        Eventually.of_forall fun n => ⟨zero_le, (dyadicTime_lowerDyadic_le u n).trans hu.2⟩⟩
    refine mem_closure_of_tendsto ((hc u hu).tendsto.comp ht) ?_
    exact Eventually.of_forall fun n => ⟨lowerDyadic u n,
      by dsimp; rw [min_eq_left ((dyadicTime_lowerDyadic_le u n).trans hu.2)]⟩

end InteractingSLE.Sec5.Aux61SlitW
