import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCChooseSlack

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
universe u

private theorem laneC_nearIdx_nonempty (K : ℕ) : (T20B.nearIdx K).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp only [T20B.nearIdx, Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor <;> norm_num

 

theorem laneC_normalized_around_max_L2_rate_of_B3_J1_inputs
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
      (∫⁻ ω, ((T20B.nearIdx K).sup' (laneC_nearIdx_nonempty K)
        (fun b => laneCNormalizedAroundProduct P W hW Qψ (ξ : ℝ)
          p n K m b ω)) ^ (2 : ℝ) ∂P) ≤
        ENNReal.ofReal ((2 : ℝ) ^
          ((p ^ 2 * (ξ : ℝ) ^ 2 - 2 * p * (ξ : ℝ) * Q + 2 * η) * K)) := by
  obtain ⟨δ, ζ, ν, hδ, hζ, hζ1, hν, hnum⟩ :=
    laneC_exists_source_rate_slacks (ξ : ℝ) p η hp hη
  have hslack :
      ((1 + ζ) * p ^ 2 * (ξ : ℝ) ^ 2 - 2 * p * (ξ : ℝ) * Q + 2 * p * δ) +
        (4 * (ζ / (2 * (1 + ζ)))) * (ν / Real.log 2 + 1) ≤
      p ^ 2 * (ξ : ℝ) ^ 2 - 2 * p * (ξ : ℝ) * Q + 2 * η := by
    linarith
  exact laneC_normalized_around_max_L2_rate_of_B3_J1_inputs_of_slack
    Qψ hε hB3 hJ1 ξ Q hQ C p₀ p η δ ζ ν
    hC hp₀ hp₀2 hp hη hδ hζ hζ1 hν hslack

end SupercriticalLQGUniqueness.B2.DG20Conc
