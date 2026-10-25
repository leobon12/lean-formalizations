import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Inputs
import Mathlib.Topology.Instances.ENNReal.Lemmas

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Filter

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF

 

theorem laneA3_persistent_visit_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K : ℕ) (b : ℤ × ℤ) (s : ℝ)
    (hvis : ∀ j, MeasurableSet
      {ω : Ω | (ω, ω) ∈ T20C.visSet (γ j) n K b s}) :
    MeasurableSet (LaneA3Inputs.PersistentVisit γ n K b s) := by
  have heq : LaneA3Inputs.PersistentVisit γ n K b s =
      ⋃ N : ℕ, ⋂ j : ℕ,
        {ω : Ω | N ≤ j → (ω, ω) ∈ T20C.visSet (γ j) n K b s} := by
    ext ω
    simp only [LaneA3Inputs.PersistentVisit, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_iInter]
  rw [heq]
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro j
  by_cases hNj : N ≤ j
  · simpa only [hNj, true_implies] using hvis j
  · simp only [hNj, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

 

theorem laneA3_finite_persistent_visits
    {ι : Type*} (s : Finset ι) (visit : ℕ → ι → Prop)
    (h : ∀ i ∈ s, ∃ N : ℕ, ∀ j, N ≤ j → visit j i) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ i ∈ s, visit j i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ _ _ hi => by simp at hi⟩
  | @insert i s hi ih =>
    obtain ⟨Ni, hNi⟩ := h i (Finset.mem_insert_self ..)
    obtain ⟨Ns, hNs⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    refine ⟨max Ni Ns, fun j hj k hk => ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hNi j ((le_max_left _ _).trans hj)
    · exact hNs j ((le_max_right _ _).trans hj) k hk

 

theorem laneA3_mass_of_eventual_near_bounds
    (M L N : ℝ)
    (h : ∀ᶠ j : ℕ in atTop,
      M ≤ N * (1 + (((j : ℝ) + 1)⁻¹)) * L) :
    M ≤ N * L := by
  have hη : Tendsto (fun j : ℕ => (((j : ℝ) + 1)⁻¹))
      atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlim : Tendsto
      (fun j : ℕ => N * (1 + (((j : ℝ) + 1)⁻¹)) * L)
      atTop (nhds (N * L)) := by
    convert ((h1.add hη).const_mul N).mul_const L using 1 <;> ring
  exact ge_of_tendsto hlim h

end SupercriticalLQGUniqueness.B2.DG20Conc
