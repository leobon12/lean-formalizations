import SupercriticalLFPPAS.Inputs.EuclideanContinuity
import SupercriticalLFPPAS.Inputs.CompactEuclideanControl

/-! Almost-sure Euclidean regularity for a strong LQG metric. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLFPPAS.Inputs

open SupercriticalLQGUniqueness

/-- The Euclidean regularity conclusions available from the certified library,
assembled on one probability-one event.  The compact-set conclusion is a
uniform modulus statement, with no asserted power rate. -/
theorem ae_strongLQGMetric_euclideanRegularity
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : LQGMetric.DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P,
      Continuous
          (Uniqueness.BiLipschitz.Barrier.forget (D (h ω))) ∧
        B2.PfeAxioms.FinitePathsEuclideanContinuous (D (h ω)) ∧
        ∀ K : Set ℂ, IsCompact K → ∀ τ : ℝ, 0 < τ →
          ∃ c : ℝ≥0∞, 0 < c ∧
            ∀ u ∈ K, ∀ v : ℂ, D (h ω) (u, v) < c → dist u v < τ := by
  filter_upwards
    [SupercriticalLFPPAS.ae_strongLQGMetric_euclideanContinuous hD P h hh,
      ae_exists_uniform_euclidean_control hD P h hh] with ω hcont huniform
  exact ⟨hcont.1, hcont.2, huniform⟩

end SupercriticalLFPPAS.Inputs
