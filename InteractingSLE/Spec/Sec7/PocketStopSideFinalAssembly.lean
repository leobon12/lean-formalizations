/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideFinal
import InteractingSLE.Spec.Sec7.PocketStopSideFinalPieces
import InteractingSLE.Spec.Sec7.PocketStopSideCover

/-!
# Shifted canonical side limits without counterflow determination

PROVE-STRIPSYS38. The marked reference-union comparison removes both stopped-set
and reference-set field determination from the canonical pocket assembly. The
filled-hull separation is required only inside the pocket, and real corners reduce
to the incoming seed. The companion geometry module supplies the closed-pocket
and R67 left-stop identities for both pocket types.

The named inputs below are still mathematical obligations: Jordan inverse
extension, the seed's force-mark exclusion, wall face labels, incident rational
filled-hull references, their own heights and inherited arguments, phase zero,
and marked locality of each reference union with both set marks. The last is the
law at the maximum of T⁰(q) and the ordinary reference stop, not determination of
the counterflow. This file does not assert those strip-system producers.
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
theorem pocketStopSideLimit_pChart_of_marked_incident_pieces {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C Γ Fnow : Ω → Set ℂ}
    {Fold : ℚ≥0 → Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {q : ℝ≥0}
    (h𝓦 : 𝓦 ≤ mΩ) (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hc : IsPocketChartOn 𝓦 A C ψ (pChart A C ψ))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω)
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ (pChart A C ψ) q ω = C ω ∩ (H \ Fnow ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hW : PocketStopWallsLaw 𝓦 P A γ Γ Fnow h₀ q)
    (hBm : ∀ i, Measurable[mΩ, hittingSigma] (referenceSet C Fold i))
    (hBloc : ∀ i, IsLocalSet (referenceSet C Fold i) h₀ P)
    (hReferencePairLocal : ∀ i, WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (activeCompl A γ (pChart A C ψ) q) hittingSigma ⊔
        MeasurableSpace.comap (referenceSet C Fold i) hittingSigma)
      (fun ω => activeCompl A γ (pChart A C ψ) q ω ∪ referenceSet C Fold i ω) h₀ P)
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
  obtain ⟨hKm, hKloc⟩ := activeCompl_localFacts_of_wallsLaw hh₀ h𝓦 hpre hCm hCo hΓC hfr hact' hFo hW
  have hKunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion
        (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q ω)) z) :=
    Eventually.of_forall
      (not_isBounded_lowerUnion_activeCompl (q := q) hγ (fun ω hω => (hshift.1 ω hω).1))
  have hcover := pocketStopBoundaryCover_of_incident_pieces hγ (fun ω hω => (hc.1 ω hω).1)
    hact hpieces hheight hlift hword
  exact ⟨hshift, pocketStopSideLimit_of_marked_referenceCover hh₀ hKm hKloc hKunb
    hBm hBloc (fun i => by simpa only [activeCompl_shift] using hReferencePairLocal i)
    hBunb hgB hcover⟩


/-- Conditional side-limit assembly with the traversal landing input discharged
from its local drivers. The remaining named inputs are stated in full below.
Use `κ = 16 / κ_flow`, as in `exists_realization`. -/
theorem pocketStopSideLimit_pChart_of_marked_landings {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C Γ Fnow : Ω → Set ℂ}
    {Fold : ℚ≥0 → Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {q : ℝ≥0}
    (h𝓦 : 𝓦 ≤ mΩ) (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hc : IsPocketChartOn 𝓦 A C ψ (pChart A C ψ))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω)
    (hact : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ (pChart A C ψ) q ω = C ω ∩ (H \ Fnow ω))
    (hFo : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ Fnow ω))
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hW : PocketStopWallsLaw 𝓦 P A γ Γ Fnow h₀ q)
    (hBm : ∀ i, Measurable[mΩ, hittingSigma] (referenceSet C Fold i))
    (hBloc : ∀ i, IsLocalSet (referenceSet C Fold i) h₀ P)
    (hReferencePairLocal : ∀ i, WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (activeCompl A γ (pChart A C ψ) q) hittingSigma ⊔
        MeasurableSpace.comap (referenceSet C Fold i) hittingSigma)
      (fun ω => activeCompl A γ (pChart A C ψ) q ω ∪ referenceSet C Fold i ω) h₀ P)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (referenceSet C Fold i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet C Fold i ω)) z))
    {gB : CoverRef → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (referenceSet C Fold i) h₀ P (gB i))
    {faces : CoverRef → Ω → Set ℝ}
    (hJordanInverse : ∀ᵐ ω ∂P, ω ∈ A → ∃ E : ℂ → ℂ,
      EqOn E (pChart A C ψ ω).2.1 H ∧ ContinuousOn E QuantumZipper.Hbar)
    {seed : Ω → ℂ} (hPocketClosure : ∀ ω ∈ A, closure (C ω) ⊆ H ∪ {seed ω})
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
    filter_upwards [hJordanInverse, hSeedExclusion] with ω hωE hωcorner hω hq ξ hξ
    obtain ⟨E, hE, hEc⟩ := hωE hω
    obtain ⟨p, hp, ht⟩ := exists_relative_inverse_landing_in_closure (hγ ω hω) hq
      (hc.1 ω hω).1 hE hEc ξ
    exact ⟨p, relative_landing_mem_H_of_seed_exclusion (hγ ω hω) hq (hc.1 ω hω).1
      (hc.1 ω hω).2.1 (hPocketClosure ω hω) ht (hωcorner hω hq ξ hξ p ht), ht⟩
  have hpieces := incidentReferenceCover_of_landings hγ (fun ω hω => (hc.1 ω hω).1)
    hact hCo hFo hland hWallFaces hOldHullSeparation
  exact pocketStopSideLimit_pChart_of_marked_incident_pieces h𝓦 hpre hγ hc hCm hCo hΓC hfr hact hFo
    hh₀ hW hBm hBloc hReferencePairLocal hBunb hgB hpieces
    hReferenceOwnHeights hInheritedArguments hn hPhaseZero


end InteractingSLE.Sec7.PocketStopSide
