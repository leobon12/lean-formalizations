import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2
import SupercriticalLQGUniqueness.B2.PfeAxioms.RadiusBall

/-!
# Euclidean continuity for a strong LQG metric

Adapters for the Euclidean-continuity part of imported result (ii).  The
reusable library proves continuity of the identity from the LQG metric
topology to the Euclidean topology and Euclidean continuity of every finite
length metric path.  It does not provide the compact-uniform inverse-Hölder
estimate mentioned in the paper.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLFPPAS

/-- For a strong LQG metric and a normalized whole-plane GFF, almost surely
the identity from the random metric topology to the Euclidean topology is
continuous, and every finite-length metric curve is Euclidean-continuous. -/
theorem ae_strongLQGMetric_euclideanContinuous
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → SupercriticalLQGUniqueness.LSCMetric}
    (hD : SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC)
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P,
      Continuous
          (SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.forget (D (h ω))) ∧
        SupercriticalLQGUniqueness.B2.PfeAxioms.FinitePathsEuclideanContinuous
          (D (h ω)) := by
  have hWeak : SupercriticalLQGUniqueness.IsWeakLQGMetric ξ Q D :=
    SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  have hQ : 0 < Q :=
    SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.q_pos_of_weak_metric
      ξ Q D hWeak
  filter_upwards
    [SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.ae_curves_continuous
      hWeak hQ P h hh] with ω hω
  refine ⟨hω.1, ?_⟩
  intro γ a b hγ _
  exact hω.2.1 γ a b hγ

end SupercriticalLFPPAS
