import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1MaxCondMoment
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelAeMono
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1CondMoment

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

 

theorem laneC_J1_all_conditional_around_moment_event_of_J1_input
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
          P {ω | ∃ b ∈ T20B.nearIdx K,
            a < ∫⁻ x,
              ((laneC_aemeasurable_J1WeightedAround P W hW Qψ
                (ξ : ℝ) n K m b).mk
                (laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b) x) ^ q
              ∂(condExpKernel P mₛ ω)} ≤
            (ENNReal.ofReal
              (((2 : ℝ)⁻¹ ^ K * lambdaN (ξ : ℝ) W P (n - K)) ^ q) *
              ENNReal.ofReal (Real.exp (ζ * K) + 1)) / a := by
  obtain ⟨Kp, hpoint⟩ :=
    laneC_J1_all_near_blocks_le_max_log_envelope_of_J1_input
      Qψ hJ1 ξ C p hC hp hp2
  obtain ⟨Ke, hevent⟩ :=
    laneC_J1_max_conditional_envelope_event_of_J1_input
      Qψ hε hJ1 ξ C p q ζ hC hp hp2 hq hζ
  refine ⟨max Kp Ke, ?_⟩
  intro Ω mₛ mΩ _ P _ W hW hm n K m hK hK0 hKn hmK hmlo hmhi hΛ a ha0 haTop
  let Z := laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q
  let hZm := laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q
  let Z' := hZm.mk Z
  have hdom : ∀ᵐ x ∂P, ∀ b ∈ T20B.nearIdx K,
      ((laneC_aemeasurable_J1WeightedAround P W hW Qψ
        (ξ : ℝ) n K m b).mk
        (laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b) x) ^ q ≤
        Z' x := by
    have hpnt := hpoint P W hW n K m ((le_max_left _ _).trans hK)
      hK0 hKn hmK hmlo hmhi hΛ q hq.le
    have hrep : ∀ᵐ x ∂P, ∀ b ∈ T20B.nearIdx K,
        ((laneC_aemeasurable_J1WeightedAround P W hW Qψ
          (ξ : ℝ) n K m b).mk
          (laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b) x) =
        laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b x := by
      apply (Filter.eventually_all_finset (T20B.nearIdx K)).2
      intro b _
      exact (laneC_aemeasurable_J1WeightedAround P W hW Qψ
        (ξ : ℝ) n K m b).ae_eq_mk.symm
    filter_upwards [hpnt, hrep, hZm.ae_eq_mk.symm] with x hx hrepX hZeq b hb
    rw [hrepX b hb]
    exact (hx b hb).trans_eq hZeq.symm
  have hcond : ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K,
      (∫⁻ x,
        ((laneC_aemeasurable_J1WeightedAround P W hW Qψ
          (ξ : ℝ) n K m b).mk
          (laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b) x) ^ q
        ∂(condExpKernel P mₛ ω)) ≤
        ∫⁻ x, Z' x ∂(condExpKernel P mₛ ω) := by
    apply (Filter.eventually_all_finset (T20B.nearIdx K)).2
    intro b hb
    apply laneC_conditional_lintegral_mono_ae P hm
    filter_upwards [hdom] with x hx
    exact hx b hb
  have hsub : {ω | ∃ b ∈ T20B.nearIdx K,
      a < ∫⁻ x,
        ((laneC_aemeasurable_J1WeightedAround P W hW Qψ
          (ξ : ℝ) n K m b).mk
          (laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b) x) ^ q
        ∂(condExpKernel P mₛ ω)} ≤ᵐ[P]
      {ω | a < ∫⁻ x, Z' x ∂(condExpKernel P mₛ ω)} := by
    filter_upwards [hcond] with ω hω
    rintro ⟨b, hb, hbad⟩
    exact hbad.trans_le (hω b hb)
  exact (measure_mono_ae hsub).trans
    (hevent P W hW hm n K m ((le_max_right _ _).trans hK)
      hK0 hKn hmK hmlo hmhi hΛ a ha0 haTop)

end SupercriticalLQGUniqueness.B2.DG20Conc
