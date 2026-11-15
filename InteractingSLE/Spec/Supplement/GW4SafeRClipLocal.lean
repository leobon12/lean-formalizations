/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRClipSet

/-!
# GW4: marked locality reduced to live avoidance probabilities

Only nonempty open sets on the safe interval need a new component argument.
For an empty open set the Markov projection vanishes, so Doob--Dynkin supplies
the required factorization for arbitrary history marks. No determination of the
physical history by the conditional component field is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Supp8.GB6LineL

/-- The remaining conditional locality input, expressed only through live
avoidance probabilities of nonempty deterministic open subsets of `H`. -/
def SafeHullAvoidance {Ω : Type*} [MeasurableSpace Ω] (F : Frame) (ν : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (ℋ : ℝ≥0 → MeasurableSpace Ω)
    (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  ∀ t (U : Opens ℂ), (U : Set ℂ).Nonempty →
    ∀ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens,
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) ν →
      ∀ E : Set Ω, MeasurableSet[ℋ t] E →
        ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
          ν⟦{ω | lineClock F Wd GT V t ω < V ω ∧
              Disjoint (fwdHull (fun r : ℝ => R r.toNNReal ω)
                (lineClock F Wd GT V t ω).toNNReal) U} ∩ E |
            MeasurableSpace.comap h inferInstance⟧ =ᵐ[ν]
              fun ω => g (markovCompl G (h ω))

/-- On the empty open set, every conditional history probability factors
through the complementary Markov projection, with no field determination premise. -/
theorem exists_factor_condProb_of_empty {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {U : Opens ℂ} (hU : (U : Set ℂ) = ∅)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) ν)
    (E : Set Ω) :
    ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      ν⟦E | MeasurableSpace.comap h inferInstance⟧ =ᵐ[ν]
        fun ω => g (markovCompl G (h ω)) := by
  obtain ⟨g, hgm, he⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap h inferInstance) (μ := ν)
      (f := E.indicator fun _ => (1 : ℝ))).exists_eq_measurable_comp
  refine ⟨g, hgm.measurable, ?_⟩
  filter_upwards [ae_eq_zero_of_isMarkovDecomposition_empty hU hd] with ω hω
  simpa only [markovCompl, hω, sub_zero, Function.comp_apply] using congrFun he ω

/-- The live avoidance input proves marked locality of the explicit clipped
set, including the empty-open-set case and all off-safe samples. -/
theorem isHistoryAvoidanceLocal_safeHull {Ω : Type*} [MeasurableSpace Ω]
    {F : Frame} {ν : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    {ℋ : ℝ≥0 → MeasurableSpace Ω} {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    {V : Ω → ℝ≥0∞} (ha : SafeHullAvoidance F ν h ℋ Wd GT R V) (t : ℝ≥0) :
    IsHistoryAvoidanceLocal (ℋ t) (safeHull F Wd GT R V t) h ν := by
  intro U G hUH hG hd E hE
  by_cases hne : (U : Set ℂ).Nonempty
  · have he : {ω | Disjoint (safeHull F Wd GT R V t ω) U} =
        {ω | lineClock F Wd GT V t ω < V ω ∧
          Disjoint (fwdHull (fun r : ℝ => R r.toNNReal ω)
            (lineClock F Wd GT V t ω).toNNReal) U} := by
      ext ω
      simpa only [mem_ofPred_eq, disjoint_comm] using
        disjoint_safeHull_iff F Wd GT R V t ω hUH hne
    rw [he]
    exact ha t U hne G hUH hG hd E hE
  · have hU := Set.not_nonempty_iff_eq_empty.1 hne
    have he : {ω | Disjoint (safeHull F Wd GT R V t ω) U} ∩ E = E := by
      simp only [hU, disjoint_empty, ofPred_true, univ_inter]
    rw [he]
    exact exists_factor_condProb_of_empty hU hd E

end InteractingSLE.Theorem14.GW4Fix
