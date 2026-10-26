import SupercriticalConformalCovariance.Tangent.LocalFunctional
import SupercriticalConformalCovariance.Tangent.Source
import SupercriticalConformalCovariance.Lemma31.InMeasure
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import SupercriticalLQGUniqueness.B2.LscTop.Compact

/-!
# Lemma 3.3: the closed-disk metric as a local functional

`diskMetric S M` is the internal metric of `M` on the closed disk `B̄_S`, extended by `+∞`, as an
element of the Polish space `LSCFun` (`lscSection` of the closed-ball path infimum). It
is a Borel function of `M`, and for a strong LQG metric `D` the observable `g ↦ diskMetric S (D g)`
is pathwise local on every open `W ⊇ B̄_S` (Axiom II via the coin-mixture locality of the domain-metric layer, plus
the deterministic fact that the internal metric on `W` determines that on `B̄_S`). Hence
`exists_universal_local_functional` applies to it (`exists_universal_diskMetric_functional`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCMetric LSCFun IsStrongLQGMetric)
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (closedBallPathInf)
open LQGMetric (DistC IsGFFPlusCont restrictTo CoordJ)

/-- The internal metric on `B̄_S(0)`, extended by `+∞`, as a lower semicontinuous function. -/
def diskMetric (S : ℝ) (M : LSCMetric) : LSCFun :=
  SupercriticalConformalCovariance.Lemma31.lscSection (SupercriticalConformalCovariance.Lemma31.diskKernel 0 S) (SupercriticalConformalCovariance.Lemma31.diskKernel_lsc 0 S) M

theorem diskMetric_apply (S : ℝ) (M : LSCMetric) (q : ℂ × ℂ) :
    (diskMetric S M).1 q = ((closedBallPathInf M 0 S q.1 q.2 : ℝ≥0∞) : EReal) := rfl

theorem measurable_diskMetric [MeasurableSpace LSCFun] [BorelSpace LSCFun] (S : ℝ) :
    Measurable (diskMetric S) := by
  have := SupercriticalLQGUniqueness.B2.LscTop.borelSpace_LSCMetric
  exact SupercriticalConformalCovariance.Lemma31.measurable_lscSection _ (SupercriticalConformalCovariance.Lemma31.diskKernel_lsc 0 S)

/-- The closed-ball path infimum is the extended internal metric of the closed ball. -/
theorem closedBallPathInf_eq_extInternal (M : LSCMetric) (c : ℂ) (R : ℝ) (x y : ℂ) :
    closedBallPathInf M c R x y = extInternal M (closedBall c R) (x, y) := by
  unfold extInternal
  split_ifs with hq
  · rfl
  · refine eq_top_iff.2 (le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hK => le_iInf fun ha => le_iInf fun hb => ?_)
    exfalso
    refine hq ⟨?_, ?_⟩
    · rw [← ha]; exact hK a (left_mem_Icc.2 hP.1)
    · rw [← hb]; exact hK b (right_mem_Icc.2 hP.1)

/-- Equal internal metrics on `W ⊇ B̄_S` give equal closed-disk metrics. -/
theorem closedBallPathInf_eq_of_internal_eq {M₁ M₂ : LSCMetric} {W : Set ℂ}
    (h : M₁.internal W = M₂.internal W) {S : ℝ} (hSW : closedBall (0 : ℂ) S ⊆ W) :
    closedBallPathInf M₁ 0 S = closedBallPathInf M₂ 0 S := by
  have hK := SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq
    M₁ M₂ hSW h
  funext x y
  rw [closedBallPathInf_eq_extInternal, closedBallPathInf_eq_extInternal]
  unfold extInternal
  split_ifs with hq
  · rw [hK]
  · rfl

/-- **Pathwise locality of the closed-disk metric.** -/
theorem isPathwiseLocal_diskMetric {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (W : TopologicalSpace.Opens ℂ) {S : ℝ}
    (hSW : closedBall (0 : ℂ) S ⊆ W) : IsPathwiseLocal W fun g => diskMetric S (D g) := by
  intro Ω _ P _ g₁ g₂ h₁ h₂ hU
  filter_upwards [SupercriticalConformalCovariance.Domain.ae_internal_eq_of_ae_restrictTo_eq_lsc hD h₁ h₂ W hU] with ω hω
  apply Subtype.ext
  funext q
  rw [diskMetric_apply, diskMetric_apply, closedBallPathInf_eq_of_internal_eq hω hSW]

/-- **The universal closed-disk metric functional.** For countably many whole-plane GFFs plus
continuous functions and an open `W ⊇ B̄_S`, one Borel `Φ` on the coordinates of the restricted
field computes the closed-disk metric almost surely for every law. -/
theorem exists_universal_diskMetric_functional {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (W : TopologicalSpace.Opens ℂ)
    {S : ℝ} (hSW : closedBall (0 : ℂ) S ⊆ W) [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (g : ∀ i, Ω i → DistC) (hg : ∀ i, IsGFFPlusCont (g i) (P i)) :
    ∃ Φ : (CoordJ → ℝ) → LSCFun, Measurable Φ ∧
      ∀ i, ∀ᵐ ω ∂P i, diskMetric S (D (g i ω)) = Φ (locCoord W (g i ω)) := by
  haveI : StandardBorelSpace LSCFun := inferInstance
  exact exists_universal_local_functional W ((measurable_diskMetric S).comp hD.1)
    (isPathwiseLocal_diskMetric hD W hSW) ι Ω P g hg

end SupercriticalConformalCovariance.Tangent
