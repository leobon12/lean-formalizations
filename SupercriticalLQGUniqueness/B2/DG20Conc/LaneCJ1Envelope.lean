import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1MaxLogMoment
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1DistanceMoment

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

theorem laneC_J1_weighted_around_rpow_le_max_log_envelope
    (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) (b : ℤ × ℤ) (hb : b ∈ T20B.nearIdx K)
    (ω : Ω) (hfinite : laneCJ1WeightedAround Qψ ξ P W hW n K m b ω ≠ ⊤)
    (q : ℝ) (hq : 0 ≤ q) :
    laneCJ1WeightedAround Qψ ξ P W hW n K m b ω ^ q ≤
      ENNReal.ofReal
        (((2 : ℝ)⁻¹ ^ K * lambdaN ξ W P (n - K)) ^ q) *
      ENNReal.ofReal (Real.exp
        (q * laneCJ1MaxPositiveLog Qψ ξ P W hW n K m ω)) := by
  let A : ℝ := (2 : ℝ)⁻¹ ^ K * lambdaN ξ W P (n - K)
  have hA : 0 < A := mul_pos (by positivity) (lambdaN_pos hW (n - K))
  have hsingle := laneC_rpow_le_exp_positive_log hfinite hA hq
  have hX : laneCJ1PositiveLog Qψ ξ P W hW n K m b ω ≤
      laneCJ1MaxPositiveLog Qψ ξ P W hW n K m ω :=
    Finset.le_sup' (s := T20B.nearIdx K)
      (f := fun c => laneCJ1PositiveLog Qψ ξ P W hW n K m c ω) hb
  have hexp : ENNReal.ofReal
      (Real.exp (q * laneCJ1PositiveLog Qψ ξ P W hW n K m b ω)) ≤
      ENNReal.ofReal
        (Real.exp (q * laneCJ1MaxPositiveLog Qψ ξ P W hW n K m ω)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hX hq))
  have hlog : Real.log (max 1
      ((laneCJ1WeightedAround Qψ ξ P W hW n K m b ω).toReal / A)) =
      laneCJ1PositiveLog Qψ ξ P W hW n K m b ω := rfl
  rw [hlog] at hsingle
  exact hsingle.trans (mul_le_mul_of_nonneg_left hexp bot_le)

universe u

 

theorem laneC_J1_max_log_envelope_moment_of_J1_input
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
        ∀ q : ℝ, 0 < q →
          ∫⁻ ω, ENNReal.ofReal
            (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
            ENNReal.ofReal (Real.exp
              (q * laneCJ1MaxPositiveLog Qψ (ξ : ℝ) P W hW n K m ω)) ∂P ≤
            ENNReal.ofReal
              (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
            ENNReal.ofReal (Real.exp
              (q * max (laneCLogMin Qψ K)
                (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
                  (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, hmax⟩ :=
    laneC_J1_max_positive_log_moment_of_J1_input
      Qψ hJ1 ξ C p hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ q hq
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul_of_nonneg_left
    (hmax P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ q hq) bot_le

 


theorem laneC_J1_all_near_blocks_le_max_log_envelope_of_J1_input
    (Qψ : PsiParams) (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ q : ℝ, 0 ≤ q →
          ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K,
            laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b ω ^ q ≤
              ENNReal.ofReal
                (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
              ENNReal.ofReal (Real.exp
                (q * laneCJ1MaxPositiveLog Qψ (ξ : ℝ) P W hW n K m ω)) := by
  obtain ⟨K₀, hfin⟩ :=
    laneC_weighted_around_finite_of_J1_input
      Qψ hJ1 ξ C p hC hp hp2
  refine ⟨K₀, ?_⟩
  intro Ω _ P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ q hq
  have hall : ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K,
      laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b ω ≠ ⊤ := by
    apply (Filter.eventually_all_finset (T20B.nearIdx K)).2
    intro b hb
    filter_upwards [hfin P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb]
      with ω hω
    exact hω.ne
  filter_upwards [hall] with ω hω b hb
  exact laneC_J1_weighted_around_rpow_le_max_log_envelope Qψ
    (ξ : ℝ) P W hW n K m b hb ω (hω b hb) q hq

end SupercriticalLQGUniqueness.B2.DG20Conc
