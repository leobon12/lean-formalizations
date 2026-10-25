import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCAroundMeas

 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

universe u

theorem laneC_J1_positive_log_moment_of_J1_input
    (Qψ : PsiParams) (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ b ∈ T20B.nearIdx K,
        ∀ l : ℝ, 0 < l →
          ∫⁻ ω, ENNReal.ofReal (Real.exp
            (l * laneCJ1PositiveLog Qψ (ξ : ℝ) P W hW n K m b ω)) ∂P ≤
          ENNReal.ofReal (Real.exp
            (l * max (laneCLogMin Qψ K)
              (T20B.tailX0 l c₀ ((5 : ℝ) ^ K)
                (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, hmoment⟩ :=
    laneC_J1_positive_log_moment_of_aemeasurable
      Qψ hJ1 ξ C p hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb l hl
  exact hmoment P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb
    (laneC_aemeasurable_J1PositiveLog P W hW Qψ (ξ : ℝ) n K m b) l hl

end SupercriticalLQGUniqueness.B2.DG20Conc
