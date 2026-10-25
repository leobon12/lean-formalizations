import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeDecay
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_eventually_not_dyadic_bad_of_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Set Ω) (R : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hE : ∀ K, 12 ≤ K →
      P (E K) ≤ ((dyadicLatticeBox R K).card : ℝ≥0∞) *
        ENNReal.ofReal (c * Real.exp (-(120 : ℝ) *
          (sparseDyadicIndices K).card))) :
    ∀ᵐ ω ∂P, ∀ᶠ K in atTop, ω ∉ E K := by
  let F : ℕ → Set Ω := fun K => if 12 ≤ K then E K else ∅
  have hbound (K : ℕ) :
      P (F K) ≤ ENNReal.ofReal
        (((32 * R + 1) ^ 2 : ℕ) * (c * Real.exp (-(K : ℝ)))) := by
    by_cases hK : 12 ≤ K
    · have hnum := dyadic_lattice_probability_real_bound R K hK c hc
      calc
        P (F K) = P (E K) := by simp [F, hK]
        _ ≤ ((dyadicLatticeBox R K).card : ℝ≥0∞) *
          ENNReal.ofReal (c * Real.exp (-(120 : ℝ) *
            (sparseDyadicIndices K).card)) := hE K hK
        _ = ENNReal.ofReal ((dyadicLatticeBox R K).card *
            (c * Real.exp (-(120 : ℝ) *
              (sparseDyadicIndices K).card))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ _ := ENNReal.ofReal_le_ofReal hnum
    · simp [F, hK]
  have hsum : Summable (fun K : ℕ =>
      ((32 * R + 1) ^ 2 : ℕ) * (c * Real.exp (-(K : ℝ)))) := by
    simpa only [mul_assoc] using (Real.summable_exp_neg_nat.mul_left
      (((32 * R + 1) ^ 2 : ℕ) * c))
  have hfinite : (∑' K, P (F K)) ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt
      (ENNReal.tsum_le_tsum hbound) hsum.tsum_ofReal_lt_top)
  have hae := ae_eventually_notMem hfinite
  filter_upwards [hae] with ω hω
  filter_upwards [hω, eventually_ge_atTop 12] with K hnot hK
  simpa [F, hK] using hnot

end SupercriticalLQGUniqueness.B2.DG20Lim
