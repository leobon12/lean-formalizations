import SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls.ClosedBallChain
import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.ShiftFinite




 





set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls

open LQGMetric (DistC)

 

theorem ae_exists_setGeodesic_closedBalls
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (z₁ z₂ : ℂ) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (Metric.closedBall z₁ r₁)
      (Metric.closedBall z₂ r₂)) :
    ∀ᵐ ω ∂μ, ∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.SetGeodesic (D (h ω))
        (Metric.closedBall z₁ r₁) (Metric.closedBall z₂ r₂) P T := by
  have hK₁ : IsCompact (Metric.closedBall z₁ r₁) := isCompact_closedBall _ _
  have hK₂ : IsCompact (Metric.closedBall z₂ r₂) := isCompact_closedBall _ _
  have hne₁ : (Metric.closedBall z₁ r₁).Nonempty :=
    ⟨z₁, Metric.mem_closedBall_self hr₁.le⟩
  have hne₂ : (Metric.closedBall z₂ r₂).Nonempty :=
    ⟨z₂, Metric.mem_closedBall_self hr₂.le⟩
  filter_upwards [ae_setDist_closedBalls_lt_top hD μ h hh z₁ z₂ r₁ r₂
    hr₁ hr₂ hdisj, EndSaving.Choices.ae_regularAt_self hD μ h hh] with ω hfin hreg
  exact Geodesics.SetGeodesics.exists_setGeodesic_of_finite (D (h ω))
    _ _ hK₁ hK₂ hne₁ hne₂ hreg.barrier hreg.length hfin

 

theorem ae_uniqueGeodesicEventV2_closedBalls
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D D' : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (R : EndSaving.Interfaces.AdmissibleRadii)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (b : Set.Ioi (0 : ℝ))
    (z₁ z₂ : ℂ) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdisj : Disjoint (Metric.closedBall z₁ r₁)
      (Metric.closedBall z₂ r₂)) :
    ∀ᵐ ω ∂μ,
      EndSaving.Choices.UniqueGeodesicEventV2 μ h D D' ξ Q cMid par pbar R family
        b (Metric.closedBall z₁ r₁) (Metric.closedBall z₂ r₂) ω := by
  have hK₁ : IsCompact (Metric.closedBall z₁ r₁) := isCompact_closedBall _ _
  have hK₂ : IsCompact (Metric.closedBall z₂ r₂) := isCompact_closedBall _ _
  have hne₁ : (Metric.closedBall z₁ r₁).Nonempty :=
    ⟨z₁, Metric.mem_closedBall_self hr₁.le⟩
  have hne₂ : (Metric.closedBall z₂ r₂).Nonempty :=
    ⟨z₂, Metric.mem_closedBall_self hr₂.le⟩
  filter_upwards [ae_setDist_closedBalls_lt_top hD μ h hh z₁ z₂ r₁ r₂
    hr₁ hr₂ hdisj,
    Geodesics.Uniqueness.ae_uniqueGeodesicEventV2_of_base_finite hD μ h hh
      cMid par pbar R family b _ _ hK₁ hK₂ hne₁ hne₂ hdisj]
    with ω hfin huniq
  exact huniq hfin

 

theorem ae_uniqueGeodesicEventV2_closedBalls_family
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D D' : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (R : EndSaving.Interfaces.AdmissibleRadii)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (b : Set.Ioi (0 : ℝ))
    {ι : Type} [Countable ι]
    (z₁ z₂ : ι → ℂ) (r₁ r₂ : ι → ℝ)
    (hr₁ : ∀ i, 0 < r₁ i) (hr₂ : ∀ i, 0 < r₂ i)
    (hdisj : ∀ i, Disjoint (Metric.closedBall (z₁ i) (r₁ i))
      (Metric.closedBall (z₂ i) (r₂ i))) :
    ∀ᵐ ω ∂μ, ∀ i : ι,
      EndSaving.Choices.UniqueGeodesicEventV2 μ h D D' ξ Q cMid par pbar R family b
        (Metric.closedBall (z₁ i) (r₁ i))
        (Metric.closedBall (z₂ i) (r₂ i)) ω := by
  rw [ae_all_iff]
  intro i
  exact ae_uniqueGeodesicEventV2_closedBalls hD μ h hh
    cMid par pbar R family b (z₁ i) (z₂ i) (r₁ i) (r₂ i)
    (hr₁ i) (hr₂ i) (hdisj i)

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.ClosedBalls
