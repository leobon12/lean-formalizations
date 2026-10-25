import SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales.AX10Full
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids.AX11Index
import Mathlib.Analysis.Complex.ExponentialBounds




 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales

open LQGMetric (DistC addConst circleAvg)
open LQGMetric.Blueprint
open SupercriticalLQGUniqueness

 
theorem iterRadius_succ_eq_dyadic (K j : ℕ) :
    Positivity.Grids.iterRadius K (j + 1) = (dyadicRadius (K / 2 + j) : ℝ) := by
  change 2 * ((2 : ℝ) ^ (K / 2 + (j + 1)))⁻¹ =
    ((2 : ℝ) ^ (K / 2 + j))⁻¹
  rw [show K / 2 + (j + 1) = (K / 2 + j) + 1 by omega, pow_succ]
  have hp : (2 : ℝ) ^ (K / 2 + j) ≠ 0 := by positivity
  field_simp

 
theorem grid_rate_base_lt_one : 4 * Real.exp (-2) < (1 : ℝ) := by
  have h1 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have h2 : (4 : ℝ) < (Real.exp 1) ^ 2 := by nlinarith
  have he : Real.exp (2 : ℝ) = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, pow_two]
  have h4 : (4 : ℝ) < Real.exp 2 := by rwa [he]
  rw [Real.exp_neg]
  have hp := Real.exp_pos (2 : ℝ)
  exact (div_lt_iff₀ hp).2 (by simpa only [one_mul] using h4)

 
theorem ax11_grid_iteration
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ (p c₀ c : ℝ) (E : ℂ → ℕ → Set DistC),
      0 < p ∧ p < 1 ∧ 0 < c₀ ∧ 0 < c ∧
      4 * Real.exp (-2) < (1 : ℝ) ∧
      (∀ (z : ℂ) (k : ℕ),
        MeasurableSet[fieldSigma
          (fun u => addConst
            (addConst (translateDist z u) (-circleAvg u 1 z))
            (-circleAvg (addConst (translateDist z u) (-circleAvg u 1 z))
              (dyadicRadius k) 0))
          (annulus 0 ((1 / 2 : ℝ) * (dyadicRadius k : ℝ))
            ((9 / 10 : ℝ) * (dyadicRadius k : ℝ)))] (E z k)) ∧
      (∀ (z : ℂ) (k : ℕ), ENNReal.ofReal p ≤ μ (E z k)) ∧
      (∀ᵐ u ∂μ, ∀ K : ℕ, ∀ z ∈ Positivity.Grids.grid K, ∀ k : ℕ,
        u ∈ E z k → Paid ξ Q D c z (dyadicRadius k) u) ∧
      (∀ (K : ℕ), K % 2 = 0 →
        μ ({u | ∀ z ∈ Positivity.Grids.grid K,
          (3 / 4 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ) ≤
            (Positivity.Grids.scaleCount K (E z) u : ℝ)}ᶜ) ≤
          ENNReal.ofReal (2 ^ 26 * c₀ * Real.exp (-4) *
            (4 * Real.exp (-2)) ^ K)) := by
  obtain ⟨p, c₀, hp0, hp1, hc₀, hLM⟩ := Positivity.Grids.lm_dyadic_count_conditional
  obtain ⟨c, E, hc, hstrict, hprob, hpaid⟩ :=
    ax10_dyadic_events μ hμ ξ Q D hD p hp0 hp1 Positivity.Grids.grid
  refine ⟨p, c₀, c, E, hp0, hp1, hc₀, hc, grid_rate_base_lt_one,
    hstrict, hprob, hpaid, ?_⟩
  intro K hK
  let good : ℂ → Set DistC := fun z =>
    {u | (3 / 4 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ) ≤
      (Positivity.Grids.scaleCount K (E z) u : ℝ)}
  have hbad : ∀ z ∈ Positivity.Grids.grid K,
      μ ((good z)ᶜ) ≤ ENNReal.ofReal
        (c₀ * Real.exp (-4 * ((K / 2 + 1 : ℕ) : ℝ))) := by
    intro z hz
    have hfield : LQGMetric.IsNormalizedWPGFF
        (fun u : DistC => addConst (translateDist z u) (-circleAvg u 1 z)) μ :=
      normalized_translate_old hμ z
    have hs (j : ℕ) :
        MeasurableSet[fieldSigma
          (fun u => addConst
            (addConst (translateDist z u) (-circleAvg u 1 z))
            (-circleAvg (addConst (translateDist z u) (-circleAvg u 1 z))
              (Positivity.Grids.iterRadius K (j + 1)) 0))
          (annulus 0 ((1 / 2 : ℝ) * Positivity.Grids.iterRadius K (j + 1))
            ((9 / 10 : ℝ) * Positivity.Grids.iterRadius K (j + 1)))]
          (E z (K / 2 + j)) := by
      rw [iterRadius_succ_eq_dyadic]
      exact hstrict z (K / 2 + j)
    have he (j : ℕ) : ENNReal.ofReal p ≤ μ (E z (K / 2 + j)) :=
      hprob z (K / 2 + j)
    have h := hLM μ
      (fun u : DistC => addConst (translateDist z u) (-circleAvg u 1 z))
      hfield K hK (E z) hs he
    simpa only [good, Set.compl_ofPred, not_le] using h
  simpa only [good, mem_ofPred_eq] using Positivity.Grids.grid_failure_rate μ K hK good c₀ hc₀.le hbad


end SupercriticalLQGUniqueness.Uniqueness.Positivity.GoodScales
