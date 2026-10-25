import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1MaxRate
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondMomentMarkov

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

def laneCJ1MaxEnvelope (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) (q : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ)⁻¹ ^ K * lambdaN ξ W P (n - K)) ^ q) *
    ENNReal.ofReal (Real.exp
      (q * laneCJ1MaxPositiveLog Qψ ξ P W hW n K m ω))

theorem laneC_aemeasurable_J1MaxEnvelope
    (Qψ : PsiParams) (ξ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n K m : ℕ) (q : ℝ) :
    AEMeasurable (laneCJ1MaxEnvelope Qψ ξ P W hW n K m q) P := by
  exact (measurable_const.aemeasurable).mul
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable
        ((laneC_aemeasurable_J1MaxPositiveLog Qψ ξ P W hW n K m).const_mul q)))

universe u

 

theorem laneC_J1_max_conditional_envelope_event_of_J1_input
    (Qψ : PsiParams) (hε : Qψ.ε₀ < (1 : ℝ) / 100)
    (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p q ζ : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) (hq : 0 < q) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ,
      ∀ {Ω : Type u} {mₛ : MeasurableSpace Ω}
        [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W, mₛ ≤ mΩ →
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ →
          let Z := laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q
          let Z' := (laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ)
            P W hW n K m q).mk Z
          P {ω | a < ∫⁻ x, Z' x ∂(condExpKernel P mₛ ω)} ≤
            (ENNReal.ofReal
              (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
              ENNReal.ofReal (Real.exp (ζ * K) + 1)) / a := by
  obtain ⟨K₀, hmoment⟩ :=
    laneC_J1_max_log_envelope_moment_rate_of_J1_input
      Qψ hε hJ1 ξ C p q ζ hC hp hp2 hq hζ
  refine ⟨K₀, ?_⟩
  intro Ω mₛ mΩ _ P _ W hW hm n K m hK hK0 hKn hmK hmlo hmhi hΛ a ha0 haTop
  let Z := laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q
  let hZm := laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q
  let Z' := hZm.mk Z
  have hZ'm : Measurable Z' := hZm.measurable_mk
  have hZeq : Z' =ᵐ[P] Z := hZm.ae_eq_mk.symm
  calc
    P {ω | a < ∫⁻ x, Z' x ∂(condExpKernel P mₛ ω)}
        ≤ (∫⁻ x, Z' x ∂P) / a :=
          laneC_conditional_moment_markov_of_kernel P hm hZ'm ha0 haTop
    _ = (∫⁻ x, Z x ∂P) / a := by rw [lintegral_congr_ae hZeq]
    _ ≤ _ := by
      gcongr
      exact hmoment P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ

end SupercriticalLQGUniqueness.B2.DG20Conc
