import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTripleSourceBound
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCJ1Envelope

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise
universe u

 

theorem laneC_J1_all_conditional_source_products_of_J1_input
    (Qψ : PsiParams)
    (hJ1 : LaneCInputs.J1ChosenCutoffAroundTail.{u} Qψ)
    (ξ : Ioi (0 : ℝ)) (C p₀ Q δ p ζ : ℝ) (hC : 0 < C)
    (hp₀ : 0 < p₀) (hp₀2 : p₀ < 2⁻¹)
    (hp : 0 < p) (hζ : 0 < ζ) :
    ∃ K₀ : ℕ,
      ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (W : WNSpace → Ω → ℝ), ∀ hW : IsWhiteNoise P W,
      ∀ n K m : ℕ, K₀ ≤ K → 0 < K → K ≤ n → m + 1 ≤ K →
        (2 : ℝ) ^ ((m : ℝ) - 1) < (K : ℝ) ^ Qψ.ε₀ →
        (K : ℝ) ^ Qψ.ε₀ ≤ (2 : ℝ) ^ m →
        LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p₀) ≤
          Real.exp (C * Real.sqrt (K : ℝ)) →
      let q : ℝ := p * (2 * ((1 + ζ) / ζ))
      let Z := (laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ) P W hW
        n K m q).mk (laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q)
      let κ := condExpKernel P (MeasurableSpace.comap
        (fun y z => psiMN Qψ W P K n z y)
        (inferInstance : MeasurableSpace (ℂ → ℝ)))
      let R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
        (laneCB3Scale (ξ : ℝ) Q δ P W n K /
          lenObs (ξ : ℝ) (psiMN Qψ W P 0 n) (rectAB 1 1) x)
      let D (b : ℤ × ℤ) (x : Ω) :=
        (lfppContMetric (ξ : ℝ) (fun z => psiMN Qψ W P 0 n z x)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
          (LaneCInputs.sourceAround K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b)
      ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K,
        (∫⁻ x, R x ^ p * D b x ^ p ∂(κ ω)) ≤
          (∫⁻ x, (R x ^ p) ^ (2 * ((1 + ζ) / ζ)) ∂(κ ω)) ^
            (ζ / (2 * (1 + ζ))) *
          (∫⁻ x, Z x ∂(κ ω)) ^ (ζ / (2 * (1 + ζ))) *
          (ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) *
            (((1 + ζ) * p * (ξ : ℝ)) ^ 2) / 2))) ^ (1 / (1 + ζ)) := by
  obtain ⟨K₀, hpoint⟩ :=
    laneC_J1_all_near_blocks_le_max_log_envelope_of_J1_input
      Qψ hJ1 ξ C p₀ hC hp₀ hp₀2
  refine ⟨K₀, ?_⟩
  intro Ω mΩ _ P _ W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ
  let q : ℝ := p * (2 * ((1 + ζ) / ζ))
  let Z₀ := laneCJ1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q
  let hZm := laneC_aemeasurable_J1MaxEnvelope Qψ (ξ : ℝ) P W hW n K m q
  let Z := hZm.mk Z₀
  have hq : 0 ≤ q := mul_nonneg hp.le (by positivity)
  have hdom : ∀ᵐ x ∂P, ∀ b ∈ T20B.nearIdx K,
      ((laneC_aemeasurable_J1WeightedAround P W hW Qψ
        (ξ : ℝ) n K m b).mk
        (laneCJ1WeightedAround Qψ (ξ : ℝ) P W hW n K m b) x) ^ q ≤
        Z x := by
    have hpnt := hpoint P W hW n K m hK hK0 hKn hmK hmlo hmhi hΛ q hq
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
  apply (Filter.eventually_all_finset (T20B.nearIdx K)).2
  intro b hb
  exact laneC_conditional_source_product_of_envelope P W hW Qψ (ξ : ℝ)
    Q δ hKn m b p ζ hp hζ
    (by filter_upwards [hdom] with x hx; exact hx b hb)

end SupercriticalLQGUniqueness.B2.DG20Conc
