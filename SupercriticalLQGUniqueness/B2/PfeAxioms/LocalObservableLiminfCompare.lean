import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedNeighborhoodEvent
import LQGMetric.Papers.DFGPS.T12P6A

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem liminf_eq_of_eventually_mul_both {u v : ℕ → ℝ≥0∞}
    (h : ∀ c : ℝ, 1 < c →
      (∀ᶠ n in atTop, u n ≤ ENNReal.ofReal c * v n) ∧
      (∀ᶠ n in atTop, v n ≤ ENNReal.ofReal c * u n)) :
    liminf u atTop = liminf v atTop := by
  apply le_antisymm
  · apply LQGMetric.DFGPS.T12.le_of_forall_exp_mul
    intro η hη
    have hc : 1 < Real.exp (4 * η) := Real.one_lt_exp_iff.mpr (by linarith)
    have hle := (h _ hc).1
    calc
      liminf u atTop ≤ liminf (fun n => ENNReal.ofReal (Real.exp (4 * η)) * v n) atTop :=
        liminf_le_liminf hle
      _ ≤ ENNReal.ofReal (Real.exp (4 * η)) * liminf v atTop := by
        have hc0 : ENNReal.ofReal (Real.exp (4 * η)) ≠ 0 := by
          simp [Real.exp_pos]
        have hcTop : ENNReal.ofReal (Real.exp (4 * η)) ≠ ∞ := ENNReal.ofReal_ne_top
        convert
          (ENNReal.liminf_mul_le (u := fun _ : ℕ => ENNReal.ofReal (Real.exp (4 * η)))
            (v := v) (f := atTop) (Or.inl (by simpa using hc0))
            (Or.inl (by simpa using hcTop))) using 1 <;>
          (first | rfl | simp only [limsup_const])
  · apply LQGMetric.DFGPS.T12.le_of_forall_exp_mul
    intro η hη
    have hc : 1 < Real.exp (4 * η) := Real.one_lt_exp_iff.mpr (by linarith)
    have hle := (h _ hc).2
    calc
      liminf v atTop ≤ liminf (fun n => ENNReal.ofReal (Real.exp (4 * η)) * u n) atTop :=
        liminf_le_liminf hle
      _ ≤ ENNReal.ofReal (Real.exp (4 * η)) * liminf u atTop := by
        have hc0 : ENNReal.ofReal (Real.exp (4 * η)) ≠ 0 := by
          simp [Real.exp_pos]
        have hcTop : ENNReal.ofReal (Real.exp (4 * η)) ≠ ∞ := ENNReal.ofReal_ne_top
        convert
          (ENNReal.liminf_mul_le (u := fun _ : ℕ => ENNReal.ofReal (Real.exp (4 * η)))
            (v := u) (f := atTop) (Or.inl (by simpa using hc0))
            (Or.inl (by simpa using hcTop))) using 1 <;>
          (first | rfl | simp only [limsup_const])

end SupercriticalLQGUniqueness.B2.PfeAxioms
