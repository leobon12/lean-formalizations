import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldModConst
import LQGMetric.Papers.CONF.S3D114S4
import LQGMetric.Papers.GM.S4.Iterate2L420




 






set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality

 
theorem aeEventIn_shield_modConst_of_windows
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (hρr : 0 < T.rho * T.r)
    (U : Set ℂ)
    (hU : ∀ k ∈ Finset.Icc 1 Ksh,
      (shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆ U) :
    AEEventIn μ (fieldSigma0On id U)
      {g | Objects.Excursions.shield C T Ksh (D g)} := by
  let E : ℕ → Set LQGMetric.DistC := fun k =>
    if k ∈ Finset.Icc 1 Ksh then
      {g | Objects.Excursions.shieldAt C (D g) (3 * 8 ^ (Ksh - k) * (T.rho * T.r))}
    else ∅
  have hEach : ∀ k, AEEventIn μ (fieldSigma0On id U) (E k) := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 Ksh
    · simp only [E, hk, ↓reduceIte]
      have ht : 0 < 3 * 8 ^ (Ksh - k) * (T.rho * T.r) :=
        mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) hρr
      obtain ⟨R, hRm, hEq⟩ :=
        aeEventIn_shieldAt_modConst_open μ hμ ξ Q D hD C _ ht
      exact ⟨R, LQGMetric.CONF.conf36_fieldSigma0On_mono id (hU k hk) R hRm, hEq⟩
    · simp only [E, hk, ↓reduceIte]
      exact ⟨∅, @MeasurableSet.empty LQGMetric.DistC (fieldSigma0On id U), Filter.EventuallyEq.rfl⟩
  have hUnion := LQGMetric.GM.gm_aeEventIn_iUnion hEach
  have heq : {g | Objects.Excursions.shield C T Ksh (D g)} = ⋃ k, E k := by
    ext g
    simp only [Objects.Excursions.shield, E, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨k, hk, hgood⟩
      refine ⟨k, ?_⟩
      simp only [hk, ↓reduceIte, mem_ofPred_eq]
      exact hgood
    · rintro ⟨k, hgood⟩
      by_cases hk : k ∈ Finset.Icc 1 Ksh
      · exact ⟨k, hk, by simpa only [hk, ↓reduceIte, mem_ofPred_eq] using hgood⟩
      · simp only [hk, ↓reduceIte, mem_empty_iff_false] at hgood
  rw [heq]
  exact hUnion

 
theorem shieldWindow_subset_bigBall (T : Objects.CorrectedEvent.TubeData) (Ksh k : ℕ)
    (hρr : 0 < T.rho * T.r) (hk : k ∈ Finset.Icc 1 Ksh) :
    (shieldWindow (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) : Set ℂ) ⊆
      ball 0 (3 * (3 * 8 ^ Ksh) * (T.rho * T.r)) := by
  intro x hx
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkK : k ≤ Ksh := (Finset.mem_Icc.mp hk).2
  have hsub : Ksh - k + 1 ≤ Ksh := by omega
  have hpow : (8 : ℝ) ^ (Ksh - k + 1) ≤ 8 ^ Ksh :=
    pow_le_pow_right₀ (by norm_num) hsub
  rw [pow_succ] at hpow
  have hprod : (8 ^ (Ksh - k) * 8) * (T.rho * T.r) ≤
      8 ^ Ksh * (T.rho * T.r) :=
    mul_le_mul_of_nonneg_right hpow hρr.le
  have hpos : 0 < (8 : ℝ) ^ (Ksh - k) * (T.rho * T.r) :=
    mul_pos (pow_pos (by norm_num) _) hρr
  change (22 / 25) * (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) < ‖x - 0‖ ∧
    ‖x - 0‖ < (88 / 25) * (3 * 8 ^ (Ksh - k) * (T.rho * T.r)) at hx
  change dist x 0 < 3 * (3 * 8 ^ Ksh) * (T.rho * T.r)
  rw [dist_eq_norm]
  nlinarith only [hx.2, hprod, hpos]

 
theorem aeEventIn_shield_modConst_bigBall
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (hρr : 0 < T.rho * T.r) :
    AEEventIn μ
      (fieldSigma0On id (ball 0 (3 * (3 * 8 ^ Ksh) * (T.rho * T.r))))
      {g | Objects.Excursions.shield C T Ksh (D g)} := by
  exact aeEventIn_shield_modConst_of_windows μ hμ ξ Q D hD C T Ksh hρr _
    (fun k hk => shieldWindow_subset_bigBall T Ksh k hρr hk)

end SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality
