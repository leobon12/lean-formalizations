import SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids.AX11Grid
import LQGMetric.Blueprint.LMResults
import LQGMetric.Papers.LM.L3_4M6




 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open LQGMetric (DistC addConst circleAvg)
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids

 
def iterRadius (K j : ℕ) : ℝ := 2 * ((2 : ℝ) ^ (K / 2 + j))⁻¹

theorem iterRadius_pos (K j : ℕ) : 0 < iterRadius K j := by
  unfold iterRadius
  positivity

theorem iterRadius_ratio (K j : ℕ) :
    iterRadius K (j + 1) / iterRadius K j = 1 / 2 := by
  have hp : (2 : ℝ) ^ (K / 2 + j) ≠ 0 := by positivity
  unfold iterRadius
  rw [show K / 2 + (j + 1) = (K / 2 + j) + 1 by omega, pow_succ]
  field_simp

theorem iterRadius_antitone (K : ℕ) : Antitone (iterRadius K) := by
  intro i j hij
  unfold iterRadius
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

 
def paddedEvent {Ω : Type*} (K : ℕ) (E : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => Set.univ
  | j + 1 => E (K / 2 + j)

 
def scaleCount {Ω : Type} (K : ℕ) (E : ℕ → Set Ω) (ω : Ω) : ℕ := by
  classical
  exact ((Finset.Icc (K / 2) K).filter fun k => ω ∈ E k).card

theorem countOcc_padded (K : ℕ) (hK : K % 2 = 0)
    {Ω : Type} (E : ℕ → Set Ω) (ω : Ω) :
    LQGMetric.Blueprint.countOcc (paddedEvent K E) (K / 2 + 1) ω =
      scaleCount K E ω := by
  classical
  unfold LQGMetric.Blueprint.countOcc scaleCount
  apply Finset.card_bij (fun j _ => K / 2 + j - 1)
  · intro j hj
    obtain ⟨hjI, hjE⟩ := Finset.mem_filter.mp hj
    have hji := Finset.mem_Icc.mp hjI
    have heven : K / 2 + K / 2 = K := by omega
    have hidx : K / 2 + j - 1 = K / 2 + (j - 1) := by omega
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      omega
    · change ω ∈ paddedEvent K E j at hjE
      cases j with
      | zero => omega
      | succ n =>
          have hidx : K / 2 + (n + 1) - 1 = K / 2 + n := by omega
          simpa only [paddedEvent, Nat.succ_eq_add_one, hidx] using hjE
  · intro j hj i hi heq
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1).1
    omega
  · intro k hk
    obtain ⟨hkI, hkE⟩ := Finset.mem_filter.mp hk
    have hki := Finset.mem_Icc.mp hkI
    refine ⟨k - K / 2 + 1, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor <;> omega
      · rw [show k - K / 2 + 1 = (k - K / 2) + 1 by omega, paddedEvent]
        have hidx : K / 2 + (k - K / 2) = k := by omega
        simpa only [hidx] using hkE
    · omega

 
theorem padded_annulus_iter_hyp {Ω : Type} [MeasurableSpace Ω]
    (h : Ω → DistC) (K : ℕ) (E : ℕ → Set Ω)
    (hstrict : ∀ j : ℕ,
      MeasurableSet[fieldSigma
        (fun ω => addConst (h ω) (-circleAvg (h ω) (iterRadius K (j + 1)) 0))
        (annulus 0 ((1 / 2 : ℝ) * iterRadius K (j + 1))
          ((9 / 10 : ℝ) * iterRadius K (j + 1)))] (E (K / 2 + j))) :
    AnnulusIterHyp h (1 / 2) (9 / 10) (iterRadius K) (paddedEvent K E) := by
  refine ⟨iterRadius_pos K, iterRadius_antitone K, ?_, ?_⟩
  · intro j
    rw [iterRadius_ratio]
  · intro j
    cases j with
    | zero =>
        simp only [paddedEvent]
        exact MeasurableSet.univ
    | succ j =>
        simpa only [paddedEvent] using hstrict j

 
theorem lm_dyadic_count_conditional :
    ∃ p c₀ : ℝ, 0 < p ∧ p < 1 ∧ 0 < c₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (h : Ω → DistC), LQGMetric.IsNormalizedWPGFF h μ →
        ∀ (K : ℕ), K % 2 = 0 → ∀ (E : ℕ → Set Ω),
          (∀ j : ℕ,
            MeasurableSet[fieldSigma
              (fun ω => addConst (h ω) (-circleAvg (h ω) (iterRadius K (j + 1)) 0))
              (annulus 0 ((1 / 2 : ℝ) * iterRadius K (j + 1))
                ((9 / 10 : ℝ) * iterRadius K (j + 1)))] (E (K / 2 + j))) →
          (∀ j : ℕ, ENNReal.ofReal p ≤ μ (E (K / 2 + j))) →
          μ {ω | (scaleCount K E ω : ℝ) <
            (3 / 4 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ)} ≤
            ENNReal.ofReal (c₀ * Real.exp (-4 * ((K / 2 + 1 : ℕ) : ℝ))) := by
  obtain ⟨p, c₀, hp, hp1, hc₀, hmain⟩ :=
    LQGMetric.LM.lmLem3_1a (1 / 2) (9 / 10)
      (by norm_num) (by norm_num) (by norm_num)
      4 (by norm_num) (3 / 4) (by norm_num) (by norm_num)
  refine ⟨p, c₀, hp, hp1, hc₀, ?_⟩
  intro Ω mΩ μ hP h hh K hK E hstrict hprob
  have hpadprob : ∀ j, ENNReal.ofReal p ≤ μ (paddedEvent K E j) := by
    intro j
    cases j with
    | zero =>
        simp only [paddedEvent, measure_univ]
        exact ENNReal.ofReal_le_one.mpr hp1.le
    | succ j =>
        simpa only [paddedEvent] using hprob j
  have hbound := hmain μ h hh (iterRadius K) (paddedEvent K E)
    (padded_annulus_iter_hyp h K E hstrict) hpadprob (K / 2 + 1)
  have hset : {ω | (countOcc (paddedEvent K E) (K / 2 + 1) ω : ℝ) <
      (3 / 4 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ)} =
      {ω | (scaleCount K E ω : ℝ) <
        (3 / 4 : ℝ) * ((K / 2 + 1 : ℕ) : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, countOcc_padded K hK E ω]
  rwa [hset] at hbound


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids
