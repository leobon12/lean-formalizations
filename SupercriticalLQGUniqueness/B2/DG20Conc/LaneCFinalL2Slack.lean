import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCFinalRateCompare

 
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

 


theorem laneC_normalized_around_max_L2_rate_of_B3_J1_inputs_of_slack
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    (hB3 : LaneCInputs.B3SubaddTails.{u} Qψ)
    (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (C p₀ p η δ ζ ν : ℝ) (hC : 0 < C)
    (hp₀ : 0 < p₀) (hp₀2 : p₀ < 2⁻¹)
    (hp : 0 < p) (hη : 0 < η)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hζ1 : ζ < 1) (hν : 0 < ν)
    (hslack :
      ((1 + ζ) * p ^ 2 * (ξ : ℝ) ^ 2 - 2 * p * (ξ : ℝ) * Q + 2 * p * δ) +
        (4 * (ζ / (2 * (1 + ζ)))) * (ν / Real.log 2 + 1) ≤
      p ^ 2 * (ξ : ℝ) ^ 2 - 2 * p * (ξ : ℝ) * Q + 2 * η) :
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
  obtain ⟨K₀, hn⟩ := laneC_normalized_around_max_L2_of_B3_J1_inputs
    Qψ hε hB3 hJ1 ξ Q hQ C p₀ δ p ζ ν hC hp₀ hp₀2 hδ hp hζ hζ1 hν
  refine ⟨max K₀ 1, ?_⟩
  intro Ω mΩ _ P _ W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  have hell : 0 < lambdaN (ξ : ℝ) W P (n - K) := lambdaN_pos hW _
  have hbase := hn P W hW n K m ((le_max_left _ _).trans hK)
    hK0 hKn hmK hmlo hmhi hΛ
  have hK1 : 1 ≤ K := (le_max_right _ _).trans hK
  have hr : 0 ≤ 4 * (ζ / (2 * (1 + ζ))) := by
    have hden : 0 < 1 + ζ := by linarith
    positivity
  have hfactor := laneC_final_rate_compare hν.le hr hslack K hK1
  calc
    _ ≤ (ENNReal.ofReal
          (laneCB3Scale (ξ : ℝ) Q δ P W n K) ^ p)⁻¹ ^ (2 : ℝ) *
        ((ENNReal.ofReal (Real.exp (ν * K) + 1)) ^
          (2 * (ζ / (2 * (1 + ζ)))) *
          (ENNReal.ofReal
            (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^
              (p * (2 * ((1 + ζ) / ζ)))) *
            ENNReal.ofReal (Real.exp (ν * K) + 1)) ^
              (2 * (ζ / (2 * (1 + ζ)))) *
          ((ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) *
            (((1 + ζ) * p * (ξ : ℝ)) ^ 2) / 2))) ^
              (1 / (1 + ζ))) ^ (2 : ℝ)) := by
        simpa only using hbase
    _ = ENNReal.ofReal ((2 : ℝ) ^
          (((1 + ζ) * p ^ 2 * (ξ : ℝ) ^ 2 -
            2 * p * (ξ : ℝ) * Q + 2 * p * δ) * K)) *
          (ENNReal.ofReal (Real.exp (ν * K) + 1)) ^
            (4 * (ζ / (2 * (1 + ζ)))) := by
        exact laneC_normalized_L2_deterministic_rate
          (ell := lambdaN (ξ : ℝ) W P (n - K))
          (ξ := (ξ : ℝ)) (Q := Q) (δ := δ) (p := p)
          (ζ := ζ) (ν := ν) hell hp hζ K
    _ ≤ _ := hfactor

end SupercriticalLQGUniqueness.B2.DG20Conc
