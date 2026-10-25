import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.ShiftTransfer
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.WeylOrder




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric (DistC IsGFFPlusCont)

 

theorem ebl
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D') :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ z w : ℂ,
          (D' (h ω)) (z,w) ≤ ENNReal.ofReal C * (D (h ω)) (z,w) ∧
          (D (h ω)) (z,w) ≤ ENNReal.ofReal C * (D' (h ω)) (z,w) :=
  ebl_of_weyl_monotonicity weylScale_le_mul_of_pointwise ξ Q D D' hD hD'

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
