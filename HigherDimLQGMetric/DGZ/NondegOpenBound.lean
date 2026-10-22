import HigherDimLQGMetric.DGZ.NondegLimitPositive

/-! Open threshold bounds extend to the strictly positive event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

theorem nd_measure_pos_le_of_open_threshold_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ)
    (b : ℝ≥0∞)
    (hbound : ∀ ε : ℝ, 0 < ε → μ {x | ε < g x} ≤ b) :
    μ {x | 0 < g x} ≤ b := by
  let F (n : ℕ) : Set X := {x | 1 / ((n : ℝ) + 1) < g x}
  have hmono : Monotone F := by
    intro m n hmn x hx
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.succ_le_succ hmn)
    exact hfrac.trans_lt hx
  have hEq : {x : X | 0 < g x} = ⋃ n, F n := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, F]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, by simpa only [Nat.cast_add, Nat.cast_one] using hn⟩
    · rintro ⟨n, hn⟩
      exact (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans hn
  rw [hEq, hmono.measure_iUnion]
  exact iSup_le fun n => hbound _ (by positivity)

end HigherDimLQGMetric.DGZ
