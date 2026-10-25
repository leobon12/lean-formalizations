import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.PaidLimit
import LQGMetric.Papers.LM.L3_4M6
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli




 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
open LQGMetric (DistC)
open LQGMetric.Blueprint

 
theorem e1e_no_success_constants :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsNormalizedWPGFF h P →
        ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω),
          AnnulusIterHyp h (1 / 10) (4 / 5) r E →
          (∀ k, ENNReal.ofReal p ≤ P (E k)) →
          ∀ K : ℕ, 1 ≤ K →
            P {ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ E k} ≤
              ENNReal.ofReal (c * Real.exp (-(8 * Real.log 10) * K)) := by
  have hlog : 0 < 8 * Real.log 10 := by positivity
  obtain ⟨p, c, hp0, hp1, hc, H⟩ :=
    LQGMetric.LM.lmLem3_1a (1 / 10) (4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
      (8 * Real.log 10) hlog (1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, c, hp0, hp1, hc, ?_⟩
  intro Ω _ P _ h hh r E hiter hprob K hK
  have hmain := H P h hh r E hiter hprob K
  have hsub : {ω : Ω | ∀ k ∈ Finset.Icc 1 K, ω ∉ E k} ⊆
      {ω | (countOcc E K ω : ℝ) < (1 / 2 : ℝ) * K} := by
    intro ω hω
    have hz : countOcc E K ω = 0 := by
      simp only [countOcc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k hk
      exact hω k hk
    change (countOcc E K ω : ℝ) < (1 / 2 : ℝ) * K
    rw [hz]
    have : 0 < (K : ℝ) := by exact_mod_cast hK
    linarith
  exact (measure_mono hsub).trans hmain

 
theorem e1e_radii (R₀ : ℝ) (hR₀ : 0 < R₀) :
    (∀ k : ℕ, 0 < R₀ * (1 / 10 : ℝ) ^ k) ∧
    Antitone (fun k : ℕ => R₀ * (1 / 10 : ℝ) ^ k) ∧
    (∀ k : ℕ, R₀ * (1 / 10 : ℝ) ^ (k + 1) /
      (R₀ * (1 / 10 : ℝ) ^ k) ≤ 1 / 10) := by
  constructor
  · intro k; positivity
  constructor
  · intro a b hab
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hab) hR₀.le
  · intro k
    have h : 0 < R₀ * (1 / 10 : ℝ) ^ k := by positivity
    calc
      R₀ * (1 / 10 : ℝ) ^ (k + 1) / (R₀ * (1 / 10 : ℝ) ^ k)
          = (R₀ * (1 / 10 : ℝ) ^ k * (1 / 10)) /
            (R₀ * (1 / 10 : ℝ) ^ k) := by rw [pow_succ]; ring
      _ = 1 / 10 := by field_simp
      _ ≤ 1 / 10 := le_rfl

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
