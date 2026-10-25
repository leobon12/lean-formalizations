import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1Envelope
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLogMinAbsorb

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 


theorem laneC_J1_max_log_envelope_moment_rate_of_J1_input
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p q ζ : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) (hq : 0 < q) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
          ∫⁻ ω, ENNReal.ofReal
            (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
            ENNReal.ofReal (Real.exp
              (q * laneCJ1MaxPositiveLog Qψ (ξ : ℝ) P W hW n K m ω)) ∂P ≤
            ENNReal.ofReal
              (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
            ENNReal.ofReal (Real.exp (ζ * K) + 1) := by
  obtain ⟨Kj, c₀, c₁, hc₀, hc₁, hmoment⟩ :=
    laneC_J1_max_log_envelope_moment_of_J1_input
      Qψ hJ1 ξ C p hC hp hp2
  obtain ⟨Kr, hrate⟩ :=
    laneC_moment_factor_eventually_le Qψ hε hq hc₀ hc₁ hζ
  refine ⟨max Kj Kr, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  have hrate' : Real.exp (q * max (laneCLogMin Qψ K)
      (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
        (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1 ≤
        Real.exp (ζ * K) + 1 := by
    simpa only [laneC_tailX0_swap_middle q c₀ ((5 : ℝ) ^ K)
      (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀)))] using
        hrate K ((le_max_right _ _).trans hK)
  calc
    ∫⁻ ω, ENNReal.ofReal
        (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
        ENNReal.ofReal (Real.exp
          (q * laneCJ1MaxPositiveLog Qψ (ξ : ℝ) P W hW n K m ω)) ∂P
        ≤ ENNReal.ofReal
            (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
          ENNReal.ofReal (Real.exp
            (q * max (laneCLogMin Qψ K)
              (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
                (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) :=
          hmoment P W hW n K m ((le_max_left _ _).trans hK)
            hK0 hKn hmK hmlo hmhi hΛ q hq
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrate') bot_le

end SupercriticalLQGUniqueness.B2.DG20Conc
