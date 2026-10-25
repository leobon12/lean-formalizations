import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3LogTail
import LQGMetric.Papers.DDDF.S6Mul

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

theorem laneC_negative_log_tail_of_B3_input
    (Qψ : PsiParams) (hB3 : LaneCInputs.B3SubaddTails.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ C p : ℝ) (hζ : 0 < ζ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K : ℕ, K₀ ≤ K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ t : ℝ, 0 < t →
          (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < Real.exp (t / 2) →
          P {ω | t ≤ Real.log (max 1
            (((2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
                lambdaN (ξ : ℝ) W P (n - K)) /
              lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω))} ≤
            ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
              Real.exp (-(c₁ * (t / 2) ^ 2 /
                ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (t / 2))))) := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, htail⟩ :=
    hB3 ξ Q hQ ζ C p hζ hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K hK hKn hΛ t ht hT
  let L : Ω → ℝ := lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1)
  let scale : ℝ :=
    (2 : ℝ) ^ (-(1 - (ξ : ℝ) * Q + ζ) * (K : ℝ)) *
      lambdaN (ξ : ℝ) W P (n - K)
  have hL : ∀ ω, 0 < L ω := by
    intro ω
    exact lenObs_pos ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont)
      (rectAB 1 1) (by norm_num [rectAB]) (by norm_num [rectAB])
      (by norm_num [rectAB, MarkedRect.crossWidth]) ω
  have hscale : 0 < scale := by
    dsimp [scale]
    exact mul_pos (by positivity) (lambdaN_pos hW (n - K))
  have htail' : ∀ T, (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < T →
      P {ω | L ω < T⁻¹ * scale} ≤
        ENNReal.ofReal (c₀ * (5 : ℝ) ^ K *
          Real.exp (-(c₁ * (Real.log T) ^ 2 /
            ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (Real.log T))))) := by
    intro T hT'
    simpa only [L, scale, mul_assoc] using (htail P W hW n K hK hKn hΛ T hT').1
  simpa only [L, scale, neg_div, neg_mul] using
    (laneC_negative_log_tail_of_B3_tail P hL hscale
      (N := c₀) (C := (5 : ℝ) ^ K) (c := c₁)
      (a := (K : ℝ) ^ (3 * Qψ.ε₀))
      (by simpa only [neg_div, neg_mul] using htail') ht hT)

end SupercriticalLQGUniqueness.B2.DG20Conc
