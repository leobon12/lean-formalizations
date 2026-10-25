import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBRoundOsc

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 
theorem laneB_large_radius_le_one {K m : ℕ} (hKm : m + 1 ≤ K) :
    2 * (2 : ℝ)⁻¹ ^ (K - m) ≤ 1 := by
  have hpow : (2 : ℝ)⁻¹ ^ (K - m) ≤ (2 : ℝ)⁻¹ ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at hpow
  linarith

private theorem laneB_large_radius_eq {K m : ℕ} (hKm : m ≤ K) :
    2 * (2 : ℝ)⁻¹ ^ (K - m) =
      (2 : ℝ) ^ (m + 1) * (2 : ℝ)⁻¹ ^ K := by
  have hpow : (2 : ℝ)⁻¹ ^ K =
      (2 : ℝ)⁻¹ ^ (K - m) * (2 : ℝ)⁻¹ ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hKm]
  rw [hpow, pow_add]
  have hcancel : (2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    2 * (2 : ℝ)⁻¹ ^ (K - m)
      = 2 * (2 : ℝ)⁻¹ ^ (K - m) *
          ((2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ m) := by rw [hcancel, mul_one]
    _ = (2 : ℝ) ^ m * 2 ^ 1 *
          ((2 : ℝ)⁻¹ ^ (K - m) * (2 : ℝ)⁻¹ ^ m) := by norm_num; ring

 

theorem laneB_phiMN_large_annuli_gaussian_bad_event :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (K m : ℕ), m + 1 ≤ K →
    ∀ {ι : Type*} (A : ι → Set ℂ) (v : ι → ℂ) (x : ℝ),
      0 ≤ x →
      (∀ i, v i ∈ (rectAB 1 1).toSet) →
      (∀ i, A i ⊆ closedBall (v i) (2 * (2 : ℝ)⁻¹ ^ (K - m))) →
      P.real {ω | ∃ i, ∃ z ∈ A i,
        (2 : ℝ) ^ (m + 1) * x <
          |phiMN W P 0 K z ω - phiMN W P 0 K (v i) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := laneB_phiMN_round_annuli_gaussian_bad_event
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW K m hKm ι A v x hx hv hA
  apply htail hW K A v (2 * (2 : ℝ)⁻¹ ^ (K - m))
    ((2 : ℝ) ^ (m + 1)) x (laneB_large_radius_le_one hKm)
    (by positivity) hx
  · exact (laneB_large_radius_eq (by omega : m ≤ K)).le
  · exact hv
  · exact hA

end SupercriticalLQGUniqueness.B2.DG20Conc
