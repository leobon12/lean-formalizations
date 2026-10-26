import SupercriticalLFPPAS.Compare.ScaleRatio
import SupercriticalLFPPAS.Field.LocalizedApproximation
import SupercriticalLQGUniqueness.B2.Polylog.P7Trunc

/-!
# Polynomial-probability localized LFPP comparison

The `q = 1` localization in the library has cutoff radius `ε log(ε⁻¹)`, by
`Field.plRad_one_eq_localizedRadius`. The comparison event is the simultaneous pair of localized
internal-distance estimates on all endpoint pairs in a fixed bounded connected open set.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.Compare

/-- For each `ζ ∈ (0,1)`, the q=1 localized LFPP metric and the strong LQG metric satisfy
both truncation comparisons on every deterministic bounded connected open `U`, with polynomially
high probability as `ε → 0`. -/
theorem localized_comparison (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hQ : IsLFPPExponent ξ Q) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
        ∃ p₀ c₀ ε₀ : ℝ, 0 < p₀ ∧ 0 < c₀ ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
            ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
              P {ω | ¬ B2.Polylog.compareHolds
                (B2.Polylog.plLocMetric (ξ : ℝ) 1 m ε hε (h ω)) (D (h ω))
                (ε ^ (1 - ζ)) U C₀} ≤ ENNReal.ofReal (c₀ * ε ^ p₀) := by
  let hI := SupercriticalLQGUniqueness.B2.Final.dg20Interfaces_proved
  exact SupercriticalLQGUniqueness.B2.Polylog.prop_lqg_lfpp_trunc_of_inputs
    (SupercriticalLQGUniqueness.B2.Polylog.plHeatAnnulusTight_of_inputs hI.2.1 hI.1)
    (SupercriticalLQGUniqueness.B2.Polylog.plCompareSubset_of_dg20
      hI.2.1 hI.2.2.2.1
      SupercriticalLQGUniqueness.B2.QPos.dg20ExponentPositive_proved)
    hI.1 ξ Q hQ (isPfeWeakMetric_of_isStrongLQGMetric hD) m hm one_pos hζ0 hζ1

end SupercriticalLFPPAS.Compare
