import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeBox

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def dyadicLatticeCenter (K : ℕ) (v : ℤ × ℤ) : ℚ × ℚ :=
  ((v.1 : ℚ) / (2 : ℚ) ^ (K + 4),
   (v.2 : ℚ) / (2 : ℚ) ^ (K + 4))

theorem measure_exists_site_bad_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (R K : ℕ) (E : (ℤ × ℤ) → Set Ω) (b : ℝ≥0∞)
    (hsite : ∀ v ∈ dyadicLatticeBox R K, P (E v) ≤ b) :
    P {ω | ∃ v ∈ dyadicLatticeBox R K, ω ∈ E v} ≤
      ((dyadicLatticeBox R K).card : ℝ≥0∞) * b := by
  classical
  let U := dyadicLatticeBox R K
  have heq : {ω | ∃ v ∈ U, ω ∈ E v} = ⋃ v ∈ U, E v := by
    ext ω
    simp
  rw [heq]
  calc
    P (⋃ v ∈ U, E v) ≤ ∑ v ∈ U, P (E v) := measure_biUnion_finset_le U E
    _ ≤ ∑ v ∈ U, b := by
      apply Finset.sum_le_sum
      intro v hv
      exact hsite v hv
    _ = (U.card : ℝ≥0∞) * b := by simp [nsmul_eq_mul]

end SupercriticalLQGUniqueness.B2.DG20Lim
