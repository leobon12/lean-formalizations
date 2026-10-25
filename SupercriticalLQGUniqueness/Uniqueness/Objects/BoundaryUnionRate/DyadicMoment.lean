import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.ChosenAnnulusRate
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.DyadicAround




 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

private theorem dyadicQ_pos_le_one (k : ℕ) :
    0 < Objects.BoundaryUnionDyadic.dyadicQ k ∧ Objects.BoundaryUnionDyadic.dyadicQ k ≤ 1 := by
  unfold Objects.BoundaryUnionDyadic.dyadicQ
  constructor
  · positivity
  · exact pow_le_one₀ (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ≤ 1)

private theorem dyadic_center_norm_le (w : ℂ) (i : ℕ × Bool) :
    ‖Objects.BoundaryUnionDyadic.dyadicCenter w i‖ ≤ ‖w‖ := by
  obtain ⟨hq0, hq1⟩ := dyadicQ_pos_le_one i.1
  by_cases hi : i.2
  · simp only [Objects.BoundaryUnionDyadic.dyadicCenter, hi, ↓reduceIte, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hq1)]
    exact mul_le_of_le_one_left (norm_nonneg w) (by linarith)
  · calc
      ‖Objects.BoundaryUnionDyadic.dyadicCenter w i‖ = Objects.BoundaryUnionDyadic.dyadicQ i.1 * ‖w‖ := by
        simp [Objects.BoundaryUnionDyadic.dyadicCenter, hi, Real.norm_eq_abs,
          abs_of_nonneg hq0.le]
      _ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg w) hq1

theorem dyadic_around_moment_rate
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (p : ℝ) (hp : 0 < p) (hpcrit : p < 2 * Q / ξ) :
    ∃ q : ℝ, ∃ K : ENNReal, 1 < q ∧ K < ∞ ∧
      0 < (ξ : ℝ) * Q * p - q * p ^ 2 * ξ ^ 2 / 2 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (w : ℂ) (_hw : w ≠ 0) (i : ℕ × Bool),
          (∫⁻ ω, (Objects.BoundaryUnionMoments.dyadicAround (D (h ω)) w i /
              Objects.AnnulusTails.nrm ξ Q (h ω) ‖w‖ 0) ^ p ∂P) ≤
            K * ENNReal.ofReal
              (Objects.BoundaryUnionDyadic.dyadicQ i.1 ^
                (ξ * Q * p - q * p ^ 2 * ξ ^ 2 / 2)) := by
  obtain ⟨q, K, hq, hK, hγ, hMoment⟩ :=
    normalizedAroundAt_positive_rate ξ Q hQ D hD p hp hpcrit
  refine ⟨q, K, hq, hK, hγ, ?_⟩
  intro Ω _ P _ h hh w hw i
  let s : Set.Ioi (0 : ℝ) := ⟨‖w‖, norm_pos_iff.mpr hw⟩
  let a : Set.Ioi (0 : ℝ) :=
    ⟨Objects.BoundaryUnionDyadic.dyadicOuter w i,
      mul_pos (dyadicQ_pos_le_one i.1).1 s.2⟩
  have has : (a : ℝ) ≤ s := by
    change Objects.BoundaryUnionDyadic.dyadicQ i.1 * ‖w‖ ≤ ‖w‖
    exact mul_le_of_le_one_left (norm_nonneg w) (dyadicQ_pos_le_one i.1).2
  have hnear : ‖Objects.BoundaryUnionDyadic.dyadicCenter w i - 0‖ ≤ s := by
    simpa only [sub_zero, s] using dyadic_center_norm_le w i
  have hrate := hMoment P h hh a s has (Objects.BoundaryUnionDyadic.dyadicCenter w i) 0 hnear
  have hratio : (a : ℝ) / s = Objects.BoundaryUnionDyadic.dyadicQ i.1 := by
    change Objects.BoundaryUnionDyadic.dyadicQ i.1 * ‖w‖ / ‖w‖ = Objects.BoundaryUnionDyadic.dyadicQ i.1
    exact mul_div_cancel_right₀ _ s.2.ne'
  simpa only [normalizedAroundAt, Objects.BoundaryUnionMoments.dyadicAround, a, s,
    one_mul, one_div, inv_mul_eq_div, hratio] using hrate


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
