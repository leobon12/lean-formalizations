import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPositiveLogTransfer
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1InputFinite
import LQGMetric.Papers.DDDF.S6Mul

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

def laneCJ1WeightedAround (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) (b : ℤ × ℤ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-ξ * phiMN W P 0 K
    (T20.dyCenter K b) ω)) *
    (lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z ω)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont ω)).aroundDist
      (LaneCInputs.sourceAround K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b)

universe u

 


theorem laneC_J1_weighted_around_moment_of_J1_input
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
        ∀ q : ℝ, 0 < q →
          ∫⁻ ω, laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b ω ^ q ∂P ≤
            ENNReal.ofReal
              (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
            ENNReal.ofReal (Real.exp
              (q * max (laneCLogMin Qψ K)
                (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
                  (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) := by
  obtain ⟨Km, c₀, c₁, hc₀, hc₁, hmoment⟩ :=
    laneC_J1_positive_log_moment_of_J1_input Qψ hJ1 ξ C p hC hp hp2
  obtain ⟨Kf, hfinite⟩ :=
    laneC_weighted_around_finite_of_J1_input Qψ hJ1 ξ C p hC hp hp2
  refine ⟨max Km Kf, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb q hq
  let Y : Ω → ℝ≥0∞ :=
    laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b
  let A : ℝ := (2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)
  have hA : 0 < A :=
    mul_pos (by positivity) (lambdaN_pos hW (n - K))
  have hY : ∀ᵐ ω ∂P, Y ω ≠ ⊤ := by
    filter_upwards [hfinite P W hW n K m ((le_max_right _ _).trans hK)
      hK0 hKn hmK hmlo hmhi hΛ b hb] with ω hω
    exact hω.ne
  have htransfer :=
    laneC_lintegral_rpow_le_exp_positive_log P hY hA hq.le
  have hlogmoment := hmoment P W hW n K m
    ((le_max_left _ _).trans hK) hK0 hKn hmK hmlo hmhi hΛ b hb q hq
  have hsame :
      (fun ω => Real.log (max 1 ((Y ω).toReal / A))) =
        laneCJ1PositiveLog Qψ (ξ : ℝ) P W hW n K m b := by
    rfl
  simpa only [hsame, Y, A] using
    htransfer.trans (mul_le_mul_of_nonneg_left hlogmoment bot_le)

end SupercriticalLQGUniqueness.B2.DG20Conc
