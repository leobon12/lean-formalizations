import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3InputMoment
import LQGMetric.Papers.DDDF.S6Mul

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

theorem laneC_B3_ratio_moment_of_B3_input
    (Qψ : PsiParams) (hB3 : LaneCInputs.B3SubaddTails.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ C p : ℝ) (hζ : 0 < ζ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K : ℕ, K₀ ≤ K → 0 < K → K ≤ n →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ q : ℝ, 0 < q →
          ∫⁻ ω, ENNReal.ofReal
            ((laneCB3Scale (ξ : ℝ) Q ζ P W n K /
              lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω) ^ q) ∂P ≤
          ENNReal.ofReal (Real.exp (q * max (laneCLogMin Qψ K)
            (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
              (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, hmoment⟩ :=
    laneC_negative_moment_of_B3_input
      Qψ hB3 ξ Q hQ ζ C p hζ hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K hK hK0 hKn hΛ q hq
  have hscale : 0 < laneCB3Scale (ξ : ℝ) Q ζ P W n K := by
    unfold laneCB3Scale
    exact mul_pos (by positivity) (lambdaN_pos hW (n - K))
  have hpoint (ω : Ω) :
      ENNReal.ofReal
        ((laneCB3Scale (ξ : ℝ) Q ζ P W n K /
          lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω) ^ q) ≤
      ENNReal.ofReal
        (Real.exp (q * laneCB3NegativeLog Qψ (ξ : ℝ) Q ζ P W n K ω)) := by
    have hψ := isPsiVersion_psiMN (Q := Qψ) hW (Nat.zero_le n)
    have hL : 0 < lenObs (ξ : ℝ) (psiMN Qψ W P 0 n)
        (rectAB 1 1) ω :=
      lenObs_pos hψ.cont _ (by norm_num [rectAB]) (by norm_num [rectAB])
        (by norm_num [MarkedRect.crossWidth, rectAB]) ω
    let x : ℝ := laneCB3Scale (ξ : ℝ) Q ζ P W n K /
      lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω
    have hx : 0 < x := div_pos hscale hL
    have hm : 0 < max 1 x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hreal : x ^ q ≤ Real.exp (q * Real.log (max 1 x)) := by
      calc
        x ^ q ≤ (max 1 x) ^ q :=
          Real.rpow_le_rpow hx.le (le_max_right _ _) hq.le
        _ = Real.exp (q * Real.log (max 1 x)) := by
          rw [Real.rpow_def_of_pos hm]
          rw [mul_comm]
    exact ENNReal.ofReal_le_ofReal (by simpa only [x, laneCB3NegativeLog] using hreal)
  calc
    ∫⁻ ω, ENNReal.ofReal
      ((laneCB3Scale (ξ : ℝ) Q ζ P W n K /
        lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) ω) ^ q) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal
          (Real.exp (q * laneCB3NegativeLog Qψ (ξ : ℝ) Q ζ P W n K ω)) ∂P :=
          lintegral_mono hpoint
    _ ≤ _ := hmoment P W hW n K hK hK0 hKn hΛ q hq

end SupercriticalLQGUniqueness.B2.DG20Conc
