import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.B2.PfeWeyl.W1LocalBounds
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2

/-! Almost-sure uniform Euclidean control on compact sets. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLFPPAS.Inputs

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness

/-- Almost surely, on every Euclidean compact set, sufficiently small random
metric distance forces any prescribed small Euclidean distance. -/
theorem ae_exists_uniform_euclidean_control
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : LQGMetric.DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → ∀ τ : ℝ, 0 < τ →
      ∃ c : ℝ≥0∞, 0 < c ∧
        ∀ u ∈ K, ∀ v : ℂ, D (h ω) (u, v) < c → dist u v < τ := by
  have hWeak : IsWeakLQGMetric ξ Q D :=
    B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  filter_upwards [EndSaving.Choices.ae_regularAt_self hWeak P h hh] with ω hreg
  intro K hK τ hτ
  apply B2.PfeWeyl.exists_uniform_euclidean_control (D (h ω)) hreg.length
  · simpa [B2.PfeWeyl.euclidForget, BiLipschitz.Barrier.forget] using hreg.forget
  · exact hK
  · exact hτ

end SupercriticalLFPPAS.Inputs
