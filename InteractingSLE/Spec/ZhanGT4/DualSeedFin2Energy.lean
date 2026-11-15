/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Agreement
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalClock

/-!
# The actual seeded quadratic correction on a positive prefix

Packet PROVE-ZHAN-GT4-A22. Identify the difference of the original
quadratic integrals with the pathwise energy on the stopped own interval.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {κ : ℝ}

/-- The bounded original noise has exactly the energy appearing in the
actual logarithmic field formula, including both stopping endpoints. -/
theorem seedNoise_quadInt_sub (hκ : 0 ≤ κ)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d S))
    {C : ℝ} (hb : ∀ u ω, |seedNoise κ d S u ω| ≤ C)
    {ε t : ℝ≥0} (hεt : ε ≤ t) (ω : Ω) (hεS : ε ≤ S ω) :
    quadInt (seedNoise κ d S) t ω - quadInt (seedNoise κ d S) ε ω =
      κ * (∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), (d ω).ellX u ((d ω).W u) ^ 2) := by
  have hi := intervalIntegrable_time (seed_square_progressive hp) (seed_square_bound hb) ω
  have hdiff : quadInt (seedNoise κ d S) t ω - quadInt (seedNoise κ d S) ε ω =
      ∫ u in (ε : ℝ)..t, seedNoise κ d S u.toNNReal ω ^ 2 := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi 0 ε) (hi ε t)
    dsimp only [quadInt]
    linarith only [hh]
  have hval {b : ℝ≥0} (hεb : ε ≤ b) (hbS : b ≤ S ω) :
      (∫ u in (ε : ℝ)..b, seedNoise κ d S u.toNNReal ω ^ 2) =
        κ * (∫ u in (ε : ℝ)..b, (d ω).ellX u ((d ω).W u) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    rw [uIoc_of_le (show (ε : ℝ) ≤ b from hεb)] at hu
    have hu0 : 0 < u := ε.coe_nonneg.trans_lt hu.1
    have huS : u.toNNReal ≤ S ω := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hu.2.trans hbS
    simp only [seedNoise, positiveStopped, Real.toNNReal_pos.2 hu0, huS, and_self, ite_true,
      Real.coe_toNNReal _ hu0.le, mul_pow, neg_sq, Real.sq_sqrt hκ]
  rw [hdiff]
  by_cases htS : t ≤ S ω
  · rw [min_eq_left htS]
    exact hval hεt htS
  · have hSt : S ω ≤ t := le_of_not_ge htS
    have hz : (∫ u in (S ω : ℝ)..t, seedNoise κ d S u.toNNReal ω ^ 2) = 0 := by
      calc _ = ∫ _u in (S ω : ℝ)..t, (0 : ℝ) := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards [] with u hu
              rw [uIoc_of_le (show (S ω : ℝ) ≤ t from hSt)] at hu
              have huS : ¬ u.toNNReal ≤ S ω := by
                rw [Real.toNNReal_le_iff_le_coe]
                exact not_le_of_gt hu.1
              simp only [seedNoise, positiveStopped, huS, and_false, ite_false,
                zero_pow (by norm_num : 2 ≠ 0)]
        _ = 0 := intervalIntegral.integral_zero
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi ε (S ω)) (hi (S ω) t)
    rw [hz, add_zero] at hh
    rw [← hh, min_eq_right hSt]
    exact hval hεS le_rfl

end InteractingSLE.ZhanGT4
