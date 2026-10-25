import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.MetricCurveTour




 


set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour

 
theorem double_paid_sum_le {ι : Type*} (S : Finset ι) (A : ℝ) (N : ℝ≥0∞)
    (hS : S.Nonempty) (L : ι → ℝ≥0∞)
    (hL : ∀ i ∈ S, L i ≤ ENNReal.ofReal (A / (2*S.card)) * N) :
    2 * ∑ i ∈ S, L i ≤ ENNReal.ofReal A * N := by
  classical
  have hcard : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  let B : ℝ≥0∞ := ENNReal.ofReal (A / (2*S.card)) * N
  have hsum : ∑ i ∈ S, L i ≤ ∑ i ∈ S, B :=
    Finset.sum_le_sum (fun i hi => hL i hi)
  calc
    2 * ∑ i ∈ S, L i ≤ 2 * ∑ i ∈ S, B := by gcongr
    _ = (2:ℝ≥0∞) * (S.card:ℝ≥0∞) * B := by simp [B, nsmul_eq_mul, mul_assoc]
    _ = ENNReal.ofReal A * N := by
      dsimp [B]
      have hreal : 2 * (S.card:ℝ) * (A / (2*S.card)) = A := by
        field_simp
      have hscalar : (2:ℝ≥0∞) * (S.card:ℝ≥0∞) *
          ENNReal.ofReal (A/(2*S.card)) = ENNReal.ofReal A := by
        calc
          _ = ENNReal.ofReal (2 * (S.card:ℝ) * (A/(2*S.card))) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (S.card:ℝ)),
              ENNReal.ofReal_mul (by norm_num : 0 ≤ (2:ℝ))]
            norm_num
          _ = ENNReal.ofReal A := by rw [hreal]
      rw [← mul_assoc, hscalar]


end SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
