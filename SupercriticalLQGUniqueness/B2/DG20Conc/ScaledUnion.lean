import SupercriticalLQGUniqueness.B2.DG20Conc.ScaleCover

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 


theorem measure_grid_union_le_linear
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) {m : ℕ} {C R b : ℝ}
    (hR : 1 ≤ R) (hb : 0 ≤ b)
    (hm : (m : ℝ) ≤ C * R)
    (hE : ∀ j ≤ m, P (E j) ≤ ENNReal.ofReal b) :
    P (⋃ j ∈ Finset.range (m + 1), E j) ≤
      ENNReal.ofReal ((C + 1) * R * b) := by
  have hsum : P (⋃ j ∈ Finset.range (m + 1), E j) ≤
      ∑ j ∈ Finset.range (m + 1), P (E j) :=
    measure_biUnion_finset_le _ _
  have hterm : (∑ j ∈ Finset.range (m + 1), P (E j)) ≤
      (m + 1) * ENNReal.ofReal b := by
    calc
      (∑ j ∈ Finset.range (m + 1), P (E j)) ≤
          ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal b := by
            apply Finset.sum_le_sum
            intro j hj
            exact hE j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      _ = (m + 1) * ENNReal.ofReal b := by simp
  have hcount : ((m + 1 : ℕ) : ℝ) ≤ (C + 1) * R := by
    have hR0 : 0 ≤ R := by linarith
    push_cast
    nlinarith
  calc
    P (⋃ j ∈ Finset.range (m + 1), E j) ≤
        (m + 1) * ENNReal.ofReal b := hsum.trans hterm
    _ = ENNReal.ofReal (((m + 1 : ℕ) : ℝ) * b) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      norm_cast
    _ ≤ ENNReal.ofReal ((C + 1) * R * b) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcount hb)

end SupercriticalLQGUniqueness.B2.DG20Conc
