/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15

/-!
# A.1.5: the compactness step with eventually constant coordinate laws

Packet PROVE-ZHAN-GT4-A18. Source: Astra, *Follow-up proofs*, §A.1.5 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L409–L425, R38): "Regard the resulting coordinates as elements of a countable product of real standard Borel spaces.
Their marginal laws are … tight; hence the family of couplings is tight. A weak limit has the two required marginal
laws. For each fixed enclosure pair, all sufficiently late couplings have exactly the same joint law of its two recorded
stopped histories … This equality passes to the limit by continuous cylinder tests."

The couplings of the first `n` enclosure pairs do not have literally fixed marginals in the Lean set-up (the curve-`1`
marginal is the force-point law up to the last exit of the first `n` enclosures, A17's `exists_forceLaw₁`); what is
fixed is the law of every finite block of recorded coordinates from some `n` on. This file proves the compactness step
in that form:

* `isTightMeasureSet_pi_of_coord`: a set of measures on a countable product is tight if every coordinate family is;
* `isTightMeasureSet_range_of_eventually_eq`: an eventually constant sequence of finite measures on a Polish space has
  a tight range;
* **`exists_limit_of_eventually_map_eq`**: a tight sequence of probability measures on a Polish space whose
  push-forwards under countably many continuous tests are eventually constant has a limit point (a probability measure)
  with exactly those push-forwards.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace InteractingSLE.ZhanGT4

section Tight

/-- **Tightness on a countable product from tightness of every coordinate.** -/
theorem isTightMeasureSet_pi_of_coord {U : ℕ → Type*} [∀ k, TopologicalSpace (U k)] [∀ k, MeasurableSpace (U k)]
    {S : Set (Measure (∀ k, U k))} (h : ∀ k, IsTightMeasureSet ((fun μ => μ.map fun x => x k) '' S)) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  have hK : ∀ k, ∃ K : Set (U k), IsCompact K ∧ ∀ μ ∈ S, (μ.map fun x => x k) Kᶜ ≤ ε' k := fun k => by
    obtain ⟨K, hKc, hKS⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (h k)) (ε' k)
      (by exact_mod_cast hε'0 k)
    exact ⟨K, hKc, fun μ hμ => hKS _ ⟨μ, hμ, rfl⟩⟩
  choose K hKc hKS using hK
  refine ⟨Set.pi univ K, isCompact_univ_pi hKc, fun μ hμ => ?_⟩
  have e : (Set.pi univ K)ᶜ = ⋃ k, (fun x : ∀ k, U k => x k) ⁻¹' (K k)ᶜ := by
    ext x
    simp only [mem_compl_iff, Set.mem_pi, mem_univ, true_implies, not_forall, mem_iUnion, mem_preimage]
  rw [e]
  calc μ (⋃ k, (fun x : ∀ k, U k => x k) ⁻¹' (K k)ᶜ) ≤ ∑' k, μ ((fun x : ∀ k, U k => x k) ⁻¹' (K k)ᶜ) :=
        measure_iUnion_le _
    _ ≤ ∑' k, (ε' k : ℝ≥0∞) := ENNReal.tsum_le_tsum fun k =>
        (Measure.le_map_apply (measurable_pi_apply k).aemeasurable _).trans (hKS k μ hμ)
    _ ≤ ε := hε'.le

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/-- A finite set of finite measures on a Polish space is tight. -/
theorem isTightMeasureSet_of_finite {S : Set (Measure E)} (hS : S.Finite) (hfin : ∀ μ ∈ S, IsFiniteMeasure μ) :
    IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2 fun ε _ =>
      ⟨∅, isCompact_empty, fun μ hμ => absurd hμ (notMem_empty μ)⟩
  | @insert a s _ _ ih =>
    have := hfin a (mem_insert a s)
    rw [insert_eq]
    exact isTightMeasureSet_singleton.union (ih fun μ hμ => hfin μ (mem_insert_of_mem a hμ))

/-- **An eventually constant sequence of finite measures on a Polish space has a tight range.** -/
theorem isTightMeasureSet_range_of_eventually_eq (ν : ℕ → Measure E) [∀ n, IsFiniteMeasure (ν n)] {lam : Measure E}
    (hev : ∀ᶠ n in atTop, ν n = lam) : IsTightMeasureSet (range ν) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine (isTightMeasureSet_of_finite (S := ν '' Iic N) ((finite_Iic N).image ν) ?_).subset ?_
  · rintro _ ⟨n, -, rfl⟩
    infer_instance
  · rintro _ ⟨n, rfl⟩
    rcases le_total n N with h | h
    · exact ⟨n, mem_Iic.2 h, rfl⟩
    · exact ⟨N, mem_Iic.2 le_rfl, by rw [hN n h, hN N le_rfl]⟩

end Tight

section Limit

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/-- **The compactness step with eventually constant test laws.** A tight sequence of probability measures on a Polish
space whose push-forwards under countably many continuous tests `f i` are eventually equal to fixed laws `λ i` has a
cluster point (in the topology of convergence in distribution), a probability measure with push-forward `λ i` under
every `f i`. -/
theorem exists_limit_of_eventually_map_eq (μ : ℕ → ProbabilityMeasure E)
    (hT : IsTightMeasureSet (range fun n => (μ n : Measure E))) {ι : Type*} {Z : ι → Type*}
    [∀ i, TopologicalSpace (Z i)] [∀ i, MeasurableSpace (Z i)] [∀ i, BorelSpace (Z i)]
    [∀ i, HasOuterApproxClosed (Z i)] (f : ∀ i, E → Z i) (hf : ∀ i, Continuous (f i)) (lam : ∀ i, Measure (Z i))
    (hev : ∀ i, ∀ᶠ n in atTop, (μ n : Measure E).map (f i) = lam i) :
    ∃ μ' : ProbabilityMeasure E, MapClusterPt μ' atTop μ ∧ ∀ i, (μ' : Measure E).map (f i) = lam i := by
  have hT' : IsTightMeasureSet {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ range μ} :=
    hT.subset fun _ ⟨ν, ⟨n, hn⟩, e⟩ => ⟨n, by rw [← e, ← hn]⟩
  obtain ⟨μ', -, hcl⟩ := (isCompact_closure_of_isTightMeasureSet hT').exists_mapClusterPt (f := atTop) (u := μ)
    (le_principal_iff.2 (mem_map.2 (univ_mem' fun n => subset_closure ⟨n, rfl⟩)))
  refine ⟨μ', hcl, fun i => ?_⟩
  obtain ⟨n, hn⟩ := (hev i).exists
  have hP : IsProbabilityMeasure (lam i) := by
    rw [← hn]
    infer_instance
  have hC : IsClosed ((fun ν : ProbabilityMeasure E => ν.map (f i)) ⁻¹' {⟨lam i, hP⟩}) :=
    isClosed_singleton.preimage (ProbabilityMeasure.continuous_map (hf i))
  have hmem := hC.mem_of_mapClusterPt hcl ((hev i).mono fun n hn => by
    show (μ n).map (f i) = ⟨lam i, hP⟩
    exact Subtype.ext hn)
  exact congrArg Subtype.val (show (μ'.map (f i) : ProbabilityMeasure (Z i)) = ⟨lam i, hP⟩ from hmem)

end Limit

end InteractingSLE.ZhanGT4
