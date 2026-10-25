import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3InputLogTail
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCHalfLogMoment

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

def laneCB3Scale (ξ Q ζ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (n K : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(1 - ξ * Q + ζ) * (K : ℝ)) * lambdaN ξ W P (n - K)

def laneCB3NegativeLog (Qψ : PsiParams) (ξ Q ζ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (n K : ℕ) (ω : Ω) : ℝ :=
  Real.log (max 1 (laneCB3Scale ξ Q ζ P W n K /
    lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) ω))

def laneCLogMin (Qψ : PsiParams) (K : ℕ) : ℝ :=
  max 3 (2 * Real.log ((2 : ℝ) ^
    ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀))) + 1)

universe u

theorem laneC_negative_moment_of_B3_input
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
        ∀ l : ℝ, 0 < l →
          ∫⁻ ω, ENNReal.ofReal
            (Real.exp (l * laneCB3NegativeLog Qψ (ξ : ℝ) Q ζ P W n K ω)) ∂P ≤
          ENNReal.ofReal (Real.exp (l * max (laneCLogMin Qψ K)
            (T20B.tailX0 l c₀ ((5 : ℝ) ^ K)
              (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, htail⟩ :=
    laneC_negative_log_tail_of_B3_input Qψ hB3 ξ Q hQ ζ C p hζ hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω _ P W hW n K hK hK0 hKn hΛ l hl
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let X : Ω → ℝ := laneCB3NegativeLog Qψ (ξ : ℝ) Q ζ P W n K
  let L : Ω → ℝ := lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1)
  have hLm : Measurable L :=
    measurable_lenObs ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).meas) _
  have hXm : Measurable X := by
    dsimp [X, laneCB3NegativeLog]
    exact Real.measurable_log.comp
      (measurable_const.max (measurable_const.div hLm))
  have hX0 : ∀ ω, 0 ≤ X ω := by
    intro ω
    exact Real.log_nonneg (le_max_left _ _)
  have ha : 0 < (K : ℝ) ^ (3 * Qψ.ε₀) := by positivity
  have hMin2 : 2 ≤ laneCLogMin Qψ K := by
    unfold laneCLogMin
    exact (by norm_num : (2 : ℝ) ≤ 3).trans (le_max_left _ _)
  have hT : ∀ t, laneCLogMin Qψ K < t →
      (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) < Real.exp (t / 2) := by
    intro t ht
    have hbase : 0 < (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀)) := by
      positivity
    have hlt : 2 * Real.log ((2 : ℝ) ^
        ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀))) + 1 < t :=
      (le_max_right _ _).trans_lt ht
    have hlog : Real.log ((2 : ℝ) ^
        ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Qψ.ε₀))) < t / 2 := by
      linarith
    rw [← Real.exp_log hbase]
    exact Real.exp_lt_exp.mpr hlog
  have htailX : ∀ t, laneCLogMin Qψ K < t →
      P {ω | t ≤ X ω} ≤ ENNReal.ofReal
        (c₀ * (5 : ℝ) ^ K * Real.exp
          (-(c₁ * (t / 2) ^ 2 /
            ((K : ℝ) ^ (3 * Qψ.ε₀) * Real.log (t / 2))))) := by
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt (by linarith [hMin2] : 0 ≤ laneCLogMin Qψ K) ht
    simpa only [X, laneCB3NegativeLog, laneCB3Scale] using
      htail P W hW n K hK hKn hΛ t ht0 (hT t ht)
  exact laneC_exp_moment_of_half_log_tail hX0 hXm.aemeasurable
    hl hc₀.le (by positivity : 0 < (5 : ℝ) ^ K) hc₁ ha hMin2 htailX

end SupercriticalLQGUniqueness.B2.DG20Conc
