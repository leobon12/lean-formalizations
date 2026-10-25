import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLogMinAbsorb
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3RatioMoment
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1DistanceMoment

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

theorem laneC_B3_ratio_moment_rate_of_B3_input
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    (hB3 : LaneCInputs.B3SubaddTails.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (δ C p q ζ : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) (hq : 0 < q) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K : ℕ, K₀ ≤ K → 0 < K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
          ∫⁻ ω, ENNReal.ofReal
            ((laneCB3Scale (ξ : ℝ) Q δ P W n K /
              lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω) ^ q) ∂P ≤
            ENNReal.ofReal (Real.exp (ζ * K) + 1) := by
  obtain ⟨Kb, c₀, c₁, hc₀, hc₁, hmoment⟩ :=
    laneC_B3_ratio_moment_of_B3_input
      Qψ hB3 ξ Q hQ δ C p hδ hC hp hp2
  obtain ⟨Kr, hrate⟩ :=
    laneC_moment_factor_eventually_le Qψ hε hq hc₀ hc₁ hζ
  refine ⟨max Kb Kr, ?_⟩
  intro Ω _ P W hW n K hK hK0 hKn hΛ
  have hrate' : Real.exp (q * max (laneCLogMin Qψ K)
      (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
        (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1 ≤
        Real.exp (ζ * K) + 1 := by
    simpa only [laneC_tailX0_swap_middle q c₀ ((5 : ℝ) ^ K)
      (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀)))] using
        hrate K ((le_max_right _ _).trans hK)
  exact (hmoment P W hW n K ((le_max_left _ _).trans hK)
    hK0 hKn hΛ q hq).trans
      (ENNReal.ofReal_le_ofReal hrate')

 


theorem laneC_J1_weighted_around_moment_rate_of_J1_input
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
        ∀ b ∈ T20B.nearIdx K,
          ∫⁻ ω, laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b ω ^ q ∂P ≤
            ENNReal.ofReal
              (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
              ENNReal.ofReal (Real.exp (ζ * K) + 1) := by
  obtain ⟨Kj, c₀, c₁, hc₀, hc₁, hmoment⟩ :=
    laneC_J1_weighted_around_moment_of_J1_input
      Qψ hJ1 ξ C p hC hp hp2
  obtain ⟨Kr, hrate⟩ :=
    laneC_moment_factor_eventually_le Qψ hε hq hc₀ hc₁ hζ
  refine ⟨max Kj Kr, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb
  have hrate' : Real.exp (q * max (laneCLogMin Qψ K)
      (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
        (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1 ≤
        Real.exp (ζ * K) + 1 := by
    simpa only [laneC_tailX0_swap_middle q c₀ ((5 : ℝ) ^ K)
      (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀)))] using
        hrate K ((le_max_right _ _).trans hK)
  calc
    ∫⁻ ω, laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b ω ^ q ∂P
        ≤ ENNReal.ofReal
            (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
          ENNReal.ofReal (Real.exp
            (q * max (laneCLogMin Qψ K)
              (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
                (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) :=
          hmoment P W hW n K m ((le_max_left _ _).trans hK)
            hK0 hKn hmK hmlo hmhi hΛ b hb q hq
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrate') bot_le

end SupercriticalLQGUniqueness.B2.DG20Conc
