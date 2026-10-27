import MatedCRTHarmonic.GMS4.Prop48CanonicalRegularitySpatial

/-!
# Source-corrected canonical Proposition 4.8 interface

The only remaining analytic input is the good-event second moment (4.38).
The regularity exponent is supplied by Proposition 4.5 before the radius;
The jointly measurable conditional mean and spatial Fubini statements are
checked independently. Source: [18, Proposition 4.8].
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4.Canonical

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The sole unfinished input to the corrected Proposition 4.8 assembly:
(4.38) for the fluctuation restricted to a measurable spatial good event.
The event's a.s. local implication is exactly what the source uses in (4.29).
The exponent is the source's `min (2q−10ζ) ζ`, independent of `ρ`. -/
def Prop48GoodEventSecondMomentInput
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (q ζ : ℝ)
    (H1 : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
      Lemma49ConditionalMoments D hγ q ζ ρ) : Prop :=
  ∀ ρ : ℝ, (hρ : ρ ∈ Ioo (0 : ℝ) 1) →
    ∀ A : ℝ, 0 < A →
      (∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) (H1 ρ hρ).epsilonStar →
        ∀ z ∈ Metric.ball (0 : ℂ) ρ,
          Integrable (maskedUStar D hγ ε q ζ z) P ∧
          ∀ᵐ ω ∂P, conditionalMean D hγ ε q ζ ω z ≤ A) →
      ∃ Cvar : ℝ, 0 ≤ Cvar ∧ ∃ εvar : ℝ, 0 < εvar ∧
        ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) (min (H1 ρ hρ).epsilonStar εvar) →
          ∀ E : Set Ω, MeasurableSet E →
            (∀ᵐ ω ∂P, ω ∈ E →
              ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) ρ)),
                ω ∈ localEvent D hγ ε q ζ z) →
            ∀ domain : Set ℂ, ∀ f : ℂ → ℝ,
              GMS4.Prop48TestPairAdmissible ρ domain f →
              (∫⁻ ω in E, ENNReal.ofReal
                (primedFluctuation D hγ ε q ζ domain f ω ^ 2) ∂P) ≤
              ENNReal.ofReal (Cvar * ε ^ (GMS4.prop48RateAlpha q ζ) *
                (GMS4.prop48TestSupNorm ρ f) ^ 2)

/-- A bounded test's (4.38) rate implies the Chebyshev-ready rate whenever
The final exponent is at most one quarter of the source variance exponent. -/
theorem prop48_variance_rate_le_tail
    {ε α α₀ C N : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hα : 0 ≤ α) (hα₀ : 4 * α ≤ α₀) (hC : 0 ≤ C) :
    C * ε ^ α₀ * N ^ 2 ≤
      (ε ^ α * N) ^ 2 * (C * ε ^ α) := by
  have hpow : ε ^ α₀ ≤ ε ^ (3 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (by linarith)
  have hnonneg : 0 ≤ C * N ^ 2 := mul_nonneg hC (sq_nonneg _)
  have hrpow : ε ^ (3 * α) = (ε ^ α) ^ 3 := by
    rw [pow_three, ← Real.rpow_add hε.1, ← Real.rpow_add hε.1]
    congr 1
    ring
  calc
    C * ε ^ α₀ * N ^ 2 = (C * N ^ 2) * ε ^ α₀ := by ring
    _ ≤ (C * N ^ 2) * ε ^ (3 * α) :=
      mul_le_mul_of_nonneg_left hpow hnonneg
    _ = (ε ^ α * N) ^ 2 * (C * ε ^ α) := by rw [hrpow]; ring

end MatedCRTHarmonic.GMS4.Canonical

