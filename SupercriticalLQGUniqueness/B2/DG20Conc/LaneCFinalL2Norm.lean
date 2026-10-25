import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCFinalL2Rate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
universe u

private theorem laneC_nearIdx_nonempty_norm (K : ℕ) : (T20B.nearIdx K).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp only [T20B.nearIdx, Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor <;> norm_num

 


theorem laneC_normalized_around_max_L2_norm_of_B3_J1_inputs
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    (hB3 : LaneCInputs.B3SubaddTails.{u} Qψ)
    (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (C p₀ p η : ℝ) (hC : 0 < C)
    (hp₀ : 0 < p₀) (hp₀2 : p₀ < 2⁻¹)
    (hp : 0 < p) (hη : 0 < η) :
    ∃ K₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p₀) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
      (∫⁻ ω, ((T20B.nearIdx K).sup' (laneC_nearIdx_nonempty_norm K)
        (fun b => laneCNormalizedAroundProduct P W hW Qψ (ξ : ℝ)
          p n K m b ω)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal ((2 : ℝ) ^
          ((p ^ 2 * (ξ : ℝ) ^ 2 / 2 - p * (ξ : ℝ) * Q + η) * K)) := by
  obtain ⟨K₀, hK₀⟩ :=
    laneC_normalized_around_max_L2_rate_of_B3_J1_inputs
      Qψ hε hB3 hJ1 ξ Q hQ C p₀ p η hC hp₀ hp₀2 hp hη
  refine ⟨K₀, ?_⟩
  intro Ω _ _ P _ W hW n K m hK hKpos hKn hmK hmLo hmHi hΛ
  have hbound := hK₀ P W hW n K m hK hKpos hKn hmK hmLo hmHi hΛ
  have hpow := ENNReal.rpow_le_rpow hbound (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^
        ((p ^ 2 * (ξ : ℝ) ^ 2 - 2 * p * (ξ : ℝ) * Q + 2 * η) * K))) ^
          (1 / 2 : ℝ) := hpow
    _ = ENNReal.ofReal ((2 : ℝ) ^
        ((p ^ 2 * (ξ : ℝ) ^ 2 / 2 - p * (ξ : ℝ) * Q + η) * K)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring_nf

end SupercriticalLQGUniqueness.B2.DG20Conc
