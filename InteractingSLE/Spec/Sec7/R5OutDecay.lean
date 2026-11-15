/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlLocal

/-!
# Ambient-chart decay on a raw union complement

PROVE-R5-OUTER, R98, Astra §2. Only the ambient reference chart is
conformal. The later domain may be disconnected: its `Chart` merely
records that open domain. The access can lie in any incident component.
The retained-kernel construction and ordinary local-set real-boundary
decay give the required zero comparison, simultaneously for every access
and every harmonic representative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.R5Out

open LocalSets PocketStopSide R5Enl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M : Set Ω} {old raw : Ω → Chart} {gOld gRaw : Ω → DistOn upperHalfPlaneOpens}

/-- The ambient half-disc comparison along arbitrary accesses through the
raw union complement. No conformality or connectedness of `raw.dom` is
required. In particular this applies before selecting its target component. -/
theorem ae_physical_germ_along_access_of_increment_law
    (hOld : ∀ ω ∈ M, (old ω).IsConformal)
    (hInclusion : ∀ ω ∈ M, ((raw ω).dom : Set ℂ) ⊆ (old ω).dom)
    (hLaw : HasOldChartIncrementLaw P M old raw gOld gRaw) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ vOld vRaw : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vOld (old ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (old ω).dom →
        gOld ω φ = ∫ z, vOld z * φ z) →
      InnerProductSpace.HarmonicOnNhd vRaw (raw ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (raw ω).dom →
        gRaw ω φ = ∫ z, vRaw z * φ z) → ∀ (ξ x r : ℝ) (F : ℂ → ℂ),
      0 < r → (old ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (raw ω).dom →
      (∀ᶠ z in 𝓝[H] (ξ : ℂ), F z ∈ (raw ω).dom) →
      Tendsto (fun z => (old ω).1 (F z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun z => vRaw (F z) - vOld (F z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨A, residual, increment, hZero, hMeas, hRegular, hMean, hIdentity⟩ := hLaw
  have hGermLaw : IsGermConditionalLaw A residual P := ⟨increment, hMean⟩
  have hLocal : IsLocalSet A residual P :=
    ((isLocalSet_tfae hZero hMeas hRegular).out 3 4).1 hGermLaw
  filter_upwards [ae_incident_zero_germ_of_local_increment hZero hMeas hLocal hMean, hIdentity]
    with ω hGerm hId hω vOld vRaw hvOld hRepOld hvRaw hRepRaw ξ x r F hr hDisc hF hLimit
  obtain ⟨hSet, hField⟩ := hId hω
  have hRep := pull_mean_difference_representation (hOld ω hω) (hInclusion ω hω)
    hvOld hRepOld hvRaw hRepRaw
  have hHarm : InnerProductSpace.HarmonicOnNhd
      (fun z => vRaw ((old ω).2.1 z) - vOld ((old ω).2.1 z)) (H \ A ω) := by
    simpa only [hSet, compl_oldChartAddedSet hω] using hRep.1
  have hPair (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ H \ A ω) :
      increment ω φ = ∫ z, (vRaw ((old ω).2.1 z) - vOld ((old ω).2.1 z)) * φ z := by
    rw [hField (hOld ω hω)]
    exact hRep.2 φ (by rwa [hSet, compl_oldChartAddedSet hω] at hφ)
  have hWithin : Tendsto (fun z => (old ω).1 (F z))
      (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hLimit, hF.mono fun z hz =>
      (hOld ω hω).fwd_mem (hInclusion ω hω hz)⟩
  have hAvoid : Disjoint (H ∩ ball (x : ℂ) r) (A ω) := by
    rw [hSet]
    exact oldChartAddedSet_disjoint_of_inverse_collar hω hDisc
  have h := hGerm _ hHarm hPair ξ x _ hWithin ⟨r, hr, hAvoid⟩
  refine h.congr' (hF.mono fun z hz => ?_)
  rw [(hOld ω hω).inv_fwd (hInclusion ω hω hz)]

/-- The same simultaneous ambient half-disc comparison under a retained
reference event. The event `M` may depend on later exploration. -/
theorem ae_physical_germ_along_access_of_increment_law_on
    (hOld : ∀ ω ∈ M, (old ω).IsConformal)
    (hInclusion : ∀ ω ∈ M, ((raw ω).dom : Set ℂ) ⊆ (old ω).dom)
    (hLaw : HasOldChartIncrementLawOn P M old raw gOld gRaw) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ vOld vRaw : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vOld (old ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (old ω).dom →
        gOld ω φ = ∫ z, vOld z * φ z) →
      InnerProductSpace.HarmonicOnNhd vRaw (raw ω).dom →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (raw ω).dom →
        gRaw ω φ = ∫ z, vRaw z * φ z) → ∀ (ξ x r : ℝ) (F : ℂ → ℂ),
      0 < r → (old ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (raw ω).dom →
      (∀ᶠ z in 𝓝[H] (ξ : ℂ), F z ∈ (raw ω).dom) →
      Tendsto (fun z => (old ω).1 (F z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun z => vRaw (F z) - vOld (F z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨G, hGm, hMG, hlaw⟩ := hLaw
  by_cases hPG : P G = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPG] with ω hω hM
    exact absurd (hMG hM) hω
  · have : IsProbabilityMeasure (P[|G]) := cond_isProbabilityMeasure hPG
    have h := ae_physical_germ_along_access_of_increment_law (P := P[|G]) hOld hInclusion
      (hlaw inferInstance)
    filter_upwards [ae_of_ae_cond hGm h] with ω hω hM
    exact hω (hMG hM) hM

end InteractingSLE.Sec7.R5Out
