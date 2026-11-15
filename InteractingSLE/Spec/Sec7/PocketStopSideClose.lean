/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCloseGeometry
import InteractingSLE.Spec.Sec7.PocketStopSideCloseMax
import InteractingSLE.Spec.Sec7.PocketStopSideFinalAssembly

/-!
# Side limits using the landed union laws and bounded Jordan geometry

PROVE-STRIPSYS38. The current union law is the landed STRIPSYS41 law at T(q),
transferred from the left stop by R67. The comparison unions use the maximum
with each ordinary reference stop and retain the two set marks; `CloseMax`
supplies their walls laws from the same left-stop marked Galmarino input.

For a bounded pocket the incoming inverse extension is now proved from the
Jordan coordinate. The exact remaining hypotheses below are seed/mark exclusion,
incident reference selection, own reference heights, inherited arguments and
phase alignment. The reference sets still require their individual local-set
facts and their maximum-union laws, together with measurability of both set marks
in the retained histories. `CloseMax` supplies the raw maximum walls law; its
filling and the R67 reference transfer are separate proved adapters in `CloseLaws`. This is a conditional assembly, not an unconditional strip theorem.
Here `𝓦` is the stage information and may contain the exterior germ, as required
by amended R68. Only the stage-union laws use that enlarged information; the raw
walls-law producer in `CloseMax` uses the walls information before that enlargement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The side-limit predicate for the shifted canonical pocket chart, via the original
`pocketStopSideLimit_of_marked_referenceCover`. The listed geometric and field inputs remain
separate obligations; in particular `hword` is the exact phase-zero identification. -/
theorem pocketStopSideLimit_pChart_of_reference_union_laws {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C Fnow : Ω → Set ℂ}
    {Fold : ℚ≥0 → Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hc : IsPocketChartOn 𝓦 A C ψ (pChart A C ψ))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ (pChart A C ψ) q ω = C ω ∩ (H \ Fnow ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hU : PocketStopUnionLaw 𝓦 P A γ C Fnow h₀ q)
    (hBm : ∀ i, Measurable[mΩ, hittingSigma] (referenceSet C Fold i))
    (hBloc : ∀ i, IsLocalSet (referenceSet C Fold i) h₀ P)
    {referenceInfo : CoverRef → MeasurableSpace Ω}
    (hReferenceMarks : ∀ i, MeasurableSpace.comap (activeCompl A γ (pChart A C ψ) q) hittingSigma ⊔
      MeasurableSpace.comap (referenceSet C Fold i) hittingSigma ≤
        locPrefixSigma (𝓦 ⊔ referenceInfo i) A γ q)
    (hReferenceUnionLaw : ∀ i, PocketStopUnionLaw (𝓦 ⊔ referenceInfo i) P A γ C
      (fun ω => Fnow ω ∪ referenceHull Fold i ω) h₀ q)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (referenceSet C Fold i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet C Fold i ω)) z))
    {gB : CoverRef → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (referenceSet C Fold i) h₀ P (gB i))
    {faces : CoverRef → Ω → Set ℝ}
    (hpieces : IncidentReferenceCover P A γ (pChart A C ψ) C Fnow Fold q
      (fun ω => forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)) faces)
    {u : ℂ → ℝ} {liftB : CoverRef → Ω → ℂ → ℝ} {height : CoverRef → Ω → ℝ → ℝ}
    (hheight : ReferenceHeightLimits (chiC κ) P A γ (pChart A C ψ) C Fold q u faces gB liftB height)
    {branch : CoverRef → Ω → ℝ → ℤ}
    (hlift : ReferenceLiftLimits P A γ (pChart A C ψ) q faces liftB branch)
    {n : Ω → ℤ} (hn : Measurable[𝓦] n) {a : ℝ}
    (hword : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ i ξ, ξ ∈ faces i ω → height i ω ξ + chiC κ *
        (2 * Real.pi * branch i ω ξ - 2 * Real.pi * n ω) = forceBoundaryData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ξ - a) :
    IsPocketChartOn 𝓦 A C ψ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) ∧
      PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
        (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q := by
  have hshift := isPocketChartOn_shift hc hCm hn
  have hact' : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ
      (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω = C ω ∩ (H \ Fnow ω) := hact
  obtain ⟨hKm, hKloc⟩ := activeCompl_localFacts_of_unionLaw hh₀ hpre hact' hCo hFo hU
  have hKunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion
        (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω)) z) :=
    Eventually.of_forall
      (not_isBounded_lowerUnion_activeCompl (q := q) hγ (fun ω hω => (hshift.1 ω hω).1))
  have hcover := pocketStopBoundaryCover_of_incident_pieces hγ (fun ω hω => (hc.1 ω hω).1)
    hact hpieces hheight hlift hword
  have hPair := fun i => isHistoryAvoidanceLocal_active_reference_of_unionLaw
    (G := referenceHull Fold i) (B := referenceSet C Fold i) hact (fun _ _ hz => hz.1) (fun _ _ _ => rfl)
      (hReferenceMarks i) (hReferenceUnionLaw i)
  exact ⟨hshift, pocketStopSideLimit_of_marked_referenceCover hh₀ hKm hKloc hKunb
    hBm hBloc (fun i => by simpa only [activeCompl_shift] using hPair i)
    hBunb hgB hcover⟩


/-- The bounded Jordan side-limit assembly derives its incoming inverse extension
from the existing chart data. The named remaining inputs are stated in full below.
Use `κ = 16 / κ_flow`, as in `exists_realization`. -/
theorem pocketStopSideLimit_pChart_of_bounded_jordan {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C Fnow : Ω → Set ℂ}
    {Fold : ℚ≥0 → Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {q : ℝ≥0}
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hc : IsPocketChartOn 𝓦 A C ψ (pChart A C ψ))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ (pChart A C ψ) q ω = C ω ∩ (H \ Fnow ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hU : PocketStopUnionLaw 𝓦 P A γ C Fnow h₀ q)
    (hBm : ∀ i, Measurable[mΩ, hittingSigma] (referenceSet C Fold i))
    (hBloc : ∀ i, IsLocalSet (referenceSet C Fold i) h₀ P)
    {referenceInfo : CoverRef → MeasurableSpace Ω}
    (hReferenceMarks : ∀ i, MeasurableSpace.comap (activeCompl A γ (pChart A C ψ) q) hittingSigma ⊔
      MeasurableSpace.comap (referenceSet C Fold i) hittingSigma ≤
        locPrefixSigma (𝓦 ⊔ referenceInfo i) A γ q)
    (hReferenceUnionLaw : ∀ i, PocketStopUnionLaw (𝓦 ⊔ referenceInfo i) P A γ C
      (fun ω => Fnow ω ∪ referenceHull Fold i ω) h₀ q)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (referenceSet C Fold i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet C Fold i ω)) z))
    {gB : CoverRef → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (referenceSet C Fold i) h₀ P (gB i))
    {faces : CoverRef → Ω → Set ℝ}
    {pole seed : Ω → ℂ} (hPocketBounded : ∀ ω ∈ A, IsBounded (C ω))
    (hPoleOutside : ∀ ω ∈ A, pole ω ∉ C ω)
    (hJordan : ∀ ω ∈ A, Sec6.IsJordanCoord (C ω) (pole ω) (seed ω) (ψ ω))
    (hPocketClosure : ∀ ω ∈ A, closure (C ω) ⊆ H ∪ {seed ω})
    (hSeedExclusion : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
        ∀ p : ℂ, Tendsto (relChart (pChart A C ψ) γ q ω).2.1
          (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ≠ seed ω)
    (hWallFaces : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
        ∀ p ∈ frontier (C ω), p ∉ Fnow ω →
          Tendsto (relChart (pChart A C ψ) γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
            ∃ j : Fin 2, ξ ∈ faces (Sum.inl j) ω)
    (hOldHullSeparation : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
        ∀ p ∈ Fnow ω,
          Tendsto (relChart (pChart A C ψ) γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
            ∃ (s : ℚ≥0) (r : ℝ), 0 < r ∧ ξ ∈ faces (Sum.inr s) ω ∧
              Fold s ω ⊆ Fnow ω ∧ Disjoint (C ω ∩ (Fnow ω \ Fold s ω)) (ball p r))
    {u : ℂ → ℝ} {liftB : CoverRef → Ω → ℂ → ℝ} {height : CoverRef → Ω → ℝ → ℝ}
    (hReferenceOwnHeights : ReferenceHeightLimits (chiC κ) P A γ (pChart A C ψ) C Fold q u faces gB liftB height)
    {branch : CoverRef → Ω → ℝ → ℤ}
    (hInheritedArguments : ReferenceLiftLimits P A γ (pChart A C ψ) q faces liftB branch)
    {n : Ω → ℤ} (hn : Measurable[𝓦] n) {a : ℝ}
    (hPhaseZero : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ i ξ, ξ ∈ faces i ω → height i ω ξ + chiC κ *
        (2 * Real.pi * branch i ω ξ - 2 * Real.pi * n ω) = forceBoundaryData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ξ - a) :
    IsPocketChartOn 𝓦 A C ψ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) ∧
      PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
        (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q := by
  have hland : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
        ∃ p ∈ H, Tendsto (relChart (pChart A C ψ) γ q ω).2.1
          (𝓝[H] (ξ : ℂ)) (𝓝 p) := by
    filter_upwards [hSeedExclusion] with ω hωcorner hω hq ξ hξ
    obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_coord
      (hPocketBounded ω hω) (hPoleOutside ω hω) (hJordan ω hω)
      (hc.1 ω hω).1 (hc.1 ω hω).2.1 (hc.1 ω hω).2.2.1
    obtain ⟨p, hp, ht⟩ := exists_relative_inverse_landing_in_closure (hγ ω hω) hq
      (hc.1 ω hω).1 hE hEc ξ
    exact ⟨p, relative_landing_mem_H_of_seed_exclusion (hγ ω hω) hq (hc.1 ω hω).1
      (hc.1 ω hω).2.1 (hPocketClosure ω hω) ht (hωcorner hω hq ξ hξ p ht), ht⟩
  have hpieces := incidentReferenceCover_of_landings hγ (fun ω hω => (hc.1 ω hω).1)
    hact hCo hFo hland hWallFaces hOldHullSeparation
  exact pocketStopSideLimit_pChart_of_reference_union_laws hpre hγ hc hCm hCo hact hFo
    hh₀ hU hBm hBloc hReferenceMarks hReferenceUnionLaw hBunb hgB hpieces
    hReferenceOwnHeights hInheritedArguments hn hPhaseZero


end InteractingSLE.Sec7.PocketStopSide
