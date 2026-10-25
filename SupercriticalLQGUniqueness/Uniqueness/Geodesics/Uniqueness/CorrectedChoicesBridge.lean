import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.ShiftedUnique




 

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC TestC)

theorem ae_uniqueGeodesicEventV2_of_finite_distances
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
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    (hK : Disjoint K₁ K₂) :
    ∀ᵐ ω ∂μ,
      OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ < ⊤ →
      (∀ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii)
        (W : Finset (ℤ × ℤ)),
        EndSaving.Interfaces.Configuration r b K₁ K₂ W → W.Nonempty →
        OptimalConstants.Ratios.setDist
          (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r
            (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)
            W (h ω))) K₁ K₂ < ⊤) →
      EndSaving.Choices.UniqueGeodesicEventV2 μ h D D' ξ Q cMid par pbar R family
        b K₁ K₂ ω := by
  let ι := {r : Set.Ioi (0 : ℝ) | r.1 ∈ R.radii} × Finset (ℤ × ℤ)
  have : Countable {r : Set.Ioi (0 : ℝ) | r.1 ∈ R.radii} :=
    (EndSaving.Choices.admissible_countable R).to_subtype
  let ψ : ι → TestC := fun i =>
    -(EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar i.1.1
      (fun j => family (LQGMetric.GM.gridPt (((i.1.1 : Set.Ioi (0 : ℝ)) : ℝ) / 100) j)
        i.1.1 i.1.2) i.2)
  have hshift := ae_unique_set_geodesic_of_finite_set_distance_shift_family
    hD μ h hh ψ K₁ K₂ hK₁ hK₂ hne₁ hne₂ hK
  have hbase := ae_unique_set_geodesic_of_finite_set_distance hD μ h hh
    K₁ K₂ hK₁ hK₂ hne₁ hne₂ hK
  filter_upwards [hbase, hshift] with ω hbaseω hshiftω hfin hfinshift
  refine ⟨hbaseω hfin, ?_⟩
  intro r hr W hconfig hW
  have hfin' := hshiftω (⟨r, hr⟩, W) (by
    simpa only [ψ, EndSaving.FiniteEvents.subtractBumpsV2, EndSaving.Choices.subTest_eq_addFun] using
      hfinshift r hr W hconfig hW)
  simpa only [ψ, EndSaving.FiniteEvents.subtractBumpsV2, EndSaving.Choices.subTest_eq_addFun] using hfin'

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
