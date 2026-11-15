/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutAmbLaw
import InteractingSLE.Spec.Sec7.R5SameHeight

/-! # R98 §2: the raw mean agrees with the ambient reading in an empty half-disc -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMapInv fwdMap logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketStopSide PocketStopWallsFin R5Enl R5Same Aux119Heights

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {Bdrv : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}

/-- The additional comparison of R98, with the ambient original-time
chart and the raw union mean. It holds simultaneously for every half-disc,
every incident access and every harmonic representative. -/
theorem ae_tendsto_rawMean_sub_ambient_of_marked
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR Bdrv ζ h) (hκ : 0 < κ)
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0)
    (hℋ : ℋ ≤ mΩ) (hInfo : drivingFiltration P hX s ≤ ℋ)
    {B : Ω → Set ℂ} (hBm : Measurable[ℋ, hittingSigma] B)
    (hBreg : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hBloc : IsHistoryAvoidanceLocal ℋ B (centredField h u) P)
    (hSub : ∀ ω, regHull W ζ s ω ∩ H ⊆ B ω)
    {gB : Ω → DistOn upperHalfPlaneOpens} (hgB : IsLocalSetMean B (centredField h u) P gB) :
    ∀ᵐ ω ∂P, ∀ GE : ℂ → ℝ, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
        (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) GE →
      ∀ vB : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vB (H \ B ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gB ω φ = ∫ z, vB z * φ z) →
      ∀ (ξ x d : ℝ) (F : ℂ → ℂ), 0 < d →
      fwdMapInv (fun t : ℝ => W t.toNNReal ω) s '' (H ∩ ball (x : ℂ) d) ⊆ H \ B ω →
      (∀ᶠ z in 𝓝[H] (ξ : ℂ), F z ∈ H \ B ω) →
      Tendsto (fun z => fwdMap (fun t : ℝ => W t.toNNReal ω) s (F z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun z => vB (F z) + u (F z) +
        chiC κ * (logDerivFwd (fun t : ℝ => W t.toNNReal ω) s (F z)).im -
          GE (fwdMap (fun t : ℝ => W t.toNNReal ω) s (F z))) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hh0 := isZeroBoundaryGFF_centredField hC hu
  have hKm : Measurable[mΩ, hittingSigma] (regHull W ζ s) := measurable_regHull hX measurable_const
  have hKeq := (ae_regHull_eq hC hζ).mono fun ω hω => hω s
  have hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω := hζ.mono fun ω hω => by rw [hω]; exact ENNReal.coe_lt_top
  have hKl := isLocalSet_hull hC hu hX s hsζ hKeq
  obtain ⟨gK, hgK⟩ := IsLocalSet.exists_isLocalSetMean hh0 hKm hKl
  obtain ⟨G, hG, hG0, hChart, hLaw⟩ := exists_ambientRawIncrementLawOn hC hκ hu hX hζ s hℋ hInfo
    hBm hBreg hBloc hSub
  have hRawDom : ∀ ω, ((curOn univ (fun ω => H \ B ω) ω).dom : Set ℂ) = H \ B ω :=
    fun ω => dom_curOn_of_mem (mem_univ ω) (hBreg ω).2 sdiff_subset
  have hInclusion : ∀ ω ∈ G, ((curOn univ (fun ω => H \ B ω) ω).dom : Set ℂ) ⊆
      (Sec5.Markov.restartChart W (fun _ => s) ω).dom := by
    intro ω hω
    rw [hRawDom, (hChart ω hω).2]
    exact fun z hz => ⟨hz.1, fun hzK => hz.2 (hSub ω ⟨hzK, hz.1⟩)⟩
  have hDecay := ae_physical_germ_along_access_of_increment_law_on (fun ω hω => (hChart ω hω).1)
    hInclusion (hLaw gK hgK gB hgB)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := mem_ae_iff.2 hG0
  filter_upwards [hGae, hDecay, hgK.2.1, ae_eqOn_hullMean hC hκ hu hX s hsζ hKm hKeq hgK]
    with ω hω hDecay hRepK hHM GE hGE vB hvB hRepB ξ x d F hd hDisc hF hLim
  obtain ⟨hwK, hPairK⟩ := harmRep_spec hRepK
  let vK := harmRep (gK ω) (H \ regHull W ζ s ω)
  have hGerm := hDecay hω vK vB
    (by rwa [(hChart ω hω).2]) (by intro φ hφ; exact hPairK φ (by rwa [← (hChart ω hω).2]))
    (by rwa [hRawDom]) (by intro φ hφ; exact hRepB φ (by rwa [← hRawDom])) ξ x d F hd
    (by rw [hRawDom]; exact hDisc)
    (hF.mono fun z hz => by
      change F z ∈ ((curOn univ (fun ω => H \ B ω) ω).dom : Set ℂ)
      rw [hRawDom]
      exact hz) hLim
  have hMean := hHM GE hGE vK hwK hPairK
  refine hGerm.congr' (hF.mono fun z hz => ?_)
  have hzK : F z ∈ H \ regHull W ζ s ω := ⟨hz.1, fun hzK => hz.2 (hSub ω ⟨hzK, hz.1⟩)⟩
  have he := hMean hzK
  simp only [vK] at he ⊢
  rw [← he]
  ring

end InteractingSLE.Sec7.R5Out
