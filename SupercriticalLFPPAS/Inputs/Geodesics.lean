import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2
import SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics.SetGeoExists

/-! A point-pair geodesic consequence of the strong LQG metric axioms. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLFPPAS.Inputs

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness
open SupercriticalLQGUniqueness.Uniqueness.EndSaving
open SupercriticalLQGUniqueness.Uniqueness.Geodesics

/-- Almost surely, every pair at finite distance for a strong LQG metric is
joined by a length-parametrized geodesic. -/
theorem ae_exists_pointGeodesic_of_finite
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : LQGMetric.DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, D (h ω) (u, v) < ⊤ →
      ∃ γ : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.SetGeodesic (D (h ω)) {u} {v} γ T := by
  have hWeak : IsWeakLQGMetric ξ Q D :=
    B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  filter_upwards [EndSaving.Choices.ae_regularAt_self hWeak P h hh] with ω hreg
  intro u v huv
  have hsetFinite :
      OptimalConstants.Ratios.setDist (D (h ω)) ({u} : Set ℂ) ({v} : Set ℂ) < ⊤ :=
    Geodesics.SetGeodesics.setDist_lt_top_of_pair (D (h ω)) {u} {v} u v
      (Set.mem_singleton u) (Set.mem_singleton v) huv
  exact Geodesics.SetGeodesics.exists_setGeodesic_of_finite (D (h ω)) {u} {v}
    isCompact_singleton isCompact_singleton ⟨u, Set.mem_singleton u⟩
    ⟨v, Set.mem_singleton v⟩ hreg.barrier hreg.length hsetFinite

end SupercriticalLFPPAS.Inputs
