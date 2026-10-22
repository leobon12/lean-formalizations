import HigherDimLQGMetric.Locality.MovingLaw
import HigherDimLQGMetric.Locality.StageData
import LQGMetric.Prob.PolishContinuousMap

/-! Compact support turns compact-open convergence into a uniform bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_exists_bound_of_tendsto_supp {d : ℕ}
    {f : ℕ → C(Rd d, ℝ)} {F : C(Rd d, ℝ)}
    (hf : Tendsto f atTop (𝓝 F)) {K : Set (Rd d)} (hK : IsCompact K)
    (hsupp : ∀ n, ∀ z ∉ K, f n z = 0) :
    ∃ M : ℝ, (∀ n z, |f n z| ≤ M) ∧ ∀ z, |F z| ≤ M := by
  have hc : IsCompact (insert F (range f) ×ˢ K) :=
    hf.isCompact_insert_range.prod hK
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    (continuous_eval : Continuous fun p : C(Rd d, ℝ) × Rd d => p.1 p.2).continuousOn
  have hF0 : ∀ z ∉ K, F z = 0 := fun z hz =>
    tendsto_nhds_unique ((continuous_eval_const z).continuousAt.tendsto.comp hf)
      (by simp only [Function.comp_def, hsupp _ z hz]; exact tendsto_const_nhds)
  refine ⟨max C 0, fun n z => ?_, fun z => ?_⟩
  · by_cases hz : z ∈ K
    · exact (hC (f n, z) ⟨mem_insert_of_mem _ (mem_range_self n), hz⟩).trans
        (le_max_left _ _)
    · rw [hsupp n z hz, abs_zero]
      exact le_max_right _ _
  · by_cases hz : z ∈ K
    · exact (hC (F, z) ⟨mem_insert _ _, hz⟩).trans (le_max_left _ _)
    · rw [hF0 z hz, abs_zero]
      exact le_max_right _ _

/-- A convergent scalar sequence plus a compactly supported convergent
function sequence is uniformly bounded over both time and space. -/
theorem l7a_exists_bound_const_add_supp {d : ℕ}
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    {f : ℕ → C(Rd d, ℝ)} {F : C(Rd d, ℝ)}
    (hf : Tendsto f atTop (𝓝 F))
    {K : Set (Rd d)} (hK : IsCompact K)
    (hsupp : ∀ n, ∀ z ∉ K, f n z = 0) :
    ∃ M : ℝ, ∀ n z, |c n + f n z| ≤ M := by
  obtain ⟨B, hB, -⟩ := l7a_exists_bound_of_tendsto_supp hf hK hsupp
  obtain ⟨C, hC⟩ := hc.isCompact_insert_range.exists_bound_of_continuousOn
    (continuous_id : Continuous (fun x : ℝ => x)).continuousOn
  refine ⟨C + B, fun n z => ?_⟩
  exact (abs_add_le (c n) (f n z)).trans (add_le_add
    (hC (c n) (mem_insert_of_mem _ (mem_range_self n))) (hB n z))

end HigherDimLQGMetric
