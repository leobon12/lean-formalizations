/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GVanUniform
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Bases

/-! # Measurable simultaneous boundary vanishing on a compact patch

Continuity inside the domain reduces each uniform bound on an open
thickening to a fixed dense sequence. The compact-patch boundary event is
therefore a countable combination of measurable point evaluations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace Metric

namespace InteractingSLE.Sec5.Aux61GVan

/-- An interior continuous function satisfies a bound on an open set
exactly when it satisfies that bound at a dense sequence there. -/
theorem abs_le_on_open_iff_dense {U V : Set ℂ} (D : ℕ → U) (hD : DenseRange D)
    (hV : IsOpen V) {f : ℂ → ℝ} (hf : ContinuousOn f U) (ε : ℝ) :
    (∀ z ∈ U, z ∈ V → |f z| ≤ ε) ↔ ∀ n, (D n : ℂ) ∈ V → |f (D n)| ≤ ε := by
  constructor
  · exact fun h n hn => h (D n) (D n).2 hn
  · intro h z hzU hzV
    by_contra hn
    have hc : Continuous (fun p : U => |f p|) := hf.domRestrict.abs
    have ho : IsOpen {p : U | (p : ℂ) ∈ V ∧ ε < |f p|} :=
      (hV.preimage continuous_subtype_val).inter (isOpen_lt continuous_const hc)
    obtain ⟨n, hn⟩ := hD.exists_mem_open ho ⟨⟨z, hzU⟩, hzV, lt_of_not_ge hn⟩
    exact (not_lt_of_ge (h n hn.1)) hn.2

/-- For a family continuous inside a nonempty plane domain and measurable
at each interior point, vanishing simultaneously on a fixed compact patch
is a measurable event. No boundary regularity of the family is assumed. -/
theorem measurableSet_tendsto_zero_on_compact {β : Type*} [MeasurableSpace β]
    {U K : Set ℂ} (hU : U.Nonempty) (hK : IsCompact K) {F : β → ℂ → ℝ}
    (hF : ∀ z ∈ U, Measurable (fun b => F b z)) (hc : ∀ b, ContinuousOn (F b) U) :
    MeasurableSet {b | ∀ a ∈ K, Tendsto (F b) (𝓝[U] a) (𝓝 0)} := by
  have : Nonempty U := hU.to_subtype
  let D : ℕ → U := denseSeq U
  have hD : DenseRange D := denseRange_denseSeq U
  let A : Set β := ⋂ ε : ℚ, ⋂ (_ : 0 < ε), ⋃ δ : ℚ, ⋃ (_ : 0 < δ), ⋂ n : ℕ,
    {b | (D n : ℂ) ∈ thickening (δ : ℝ) K → |F b (D n)| ≤ (ε : ℝ)}
  have hm : MeasurableSet A := by
    refine MeasurableSet.iInter fun ε => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun δ => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun n => ?_
    by_cases hn : (D n : ℂ) ∈ thickening (δ : ℝ) K
    · simpa only [hn, true_implies, Function.comp_apply] using
        measurableSet_le (continuous_abs.measurable.comp (hF (D n) (D n).2)) measurable_const
    · simp only [hn, false_implies, Set.ofPred_true]
      exact MeasurableSet.univ
  have he : {b | ∀ a ∈ K, Tendsto (F b) (𝓝[U] a) (𝓝 0)} = A := by
    ext b
    simp only [A, mem_ofPred_eq, mem_iInter, mem_iUnion]
    rw [tendsto_zero_on_compact_iff hK]
    apply forall_congr'
    intro ε
    apply imp_congr_right
    intro _
    apply exists_congr
    intro δ
    simp only [exists_prop]
    apply and_congr_right
    intro _
    exact abs_le_on_open_iff_dense D hD isOpen_thickening (hc b) ε
  rw [he]
  exact hm

end InteractingSLE.Sec5.Aux61GVan
