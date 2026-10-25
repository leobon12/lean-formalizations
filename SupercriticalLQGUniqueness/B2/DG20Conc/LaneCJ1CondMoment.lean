import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1DistanceMoment
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondMomentMarkov

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

theorem laneC_aemeasurable_J1WeightedAround
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (ξ : ℝ) (n K m : ℕ) (b : ℤ × ℤ) :
    AEMeasurable (laneCJ1WeightedAround Qψ ξ P W hW n K m b) P := by
  have hφ : Measurable fun ω => phiMN W P 0 K (T20.dyCenter K b) ω :=
    (isPhiVersion_phiMN hW (Nat.zero_le K)).meas _
  have hw : Measurable fun ω =>
      ENNReal.ofReal (Real.exp (-ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hφ))
  exact hw.aemeasurable.mul
    (laneC_aemeasurable_psi_aroundDist P W hW Qψ ξ n K m b)

universe u

 


theorem laneC_J1_conditional_around_moment_event_of_J1_input
    (Qψ : PsiParams) (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p : ℝ) (hC : 0 < C)
    (hp : 0 < p) (hp2 : p < 2⁻¹) :
    ∃ K₀ : ℕ, ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type u} {mₛ : MeasurableSpace Ω}
        [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W, mₛ ≤ mΩ →
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
        ∀ b ∈ T20B.nearIdx K,
        ∀ q : ℝ, 0 < q → ∀ a : ℝ≥0∞, a ≠ 0 → a ≠ ⊤ →
          let Y := laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b
          let Y' := (laneC_aemeasurable_J1WeightedAround P W hW Qψ
            (ξ : ℝ) n K m b).mk Y
          P {ω | a < ∫⁻ x, Y' x ^ q ∂(condExpKernel P mₛ ω)} ≤
            ENNReal.ofReal
              (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
            ENNReal.ofReal (Real.exp
              (q * max (laneCLogMin Qψ K)
                (T20B.tailX0 q c₀ ((5 : ℝ) ^ K)
                  (c₁ / (4 * (K : ℝ) ^ (3 * Qψ.ε₀))))) + 1) / a := by
  obtain ⟨K₀, c₀, c₁, hc₀, hc₁, hmoment⟩ :=
    laneC_J1_weighted_around_moment_of_J1_input
      Qψ hJ1 ξ C p hC hp hp2
  refine ⟨K₀, c₀, c₁, hc₀, hc₁, ?_⟩
  intro Ω mₛ mΩ _ P _ W hW hm n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb q hq a ha0 haTop
  let Y := laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b
  let hYm := laneC_aemeasurable_J1WeightedAround P W hW Qψ (ξ : ℝ) n K m b
  let Y' := hYm.mk Y
  have hf : Measurable fun x => Y' x ^ q := by
    fun_prop
  have hfeq : (fun x => Y' x ^ q) =ᵐ[P] fun x => Y x ^ q := by
    filter_upwards [hYm.ae_eq_mk.symm] with x hx
    exact congrArg (fun z : ℝ≥0∞ => z ^ q) hx
  calc
    P {ω | a < ∫⁻ x, Y' x ^ q ∂(condExpKernel P mₛ ω)}
        ≤ (∫⁻ x, Y' x ^ q ∂P) / a :=
          laneC_conditional_moment_markov_of_kernel P hm hf ha0 haTop
    _ = (∫⁻ x, Y x ^ q ∂P) / a := by rw [lintegral_congr_ae hfeq]
    _ ≤ _ := by
      gcongr
      exact hmoment P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ b hb q hq

end SupercriticalLQGUniqueness.B2.DG20Conc
