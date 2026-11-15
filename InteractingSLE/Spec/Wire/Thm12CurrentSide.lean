/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideEnd

/-! # Remaining raw reference inputs for the pocket side limits -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open LocalSets WholeField Sec7.PocketTraversal Sec7.PocketAdapt Sec7.Lemma71C
  Sec7.PocketStop Sec7.PocketUnionPt Sec7.PocketStopField Sec7.PocketCoupling
  Sec7.PocketStopSide

namespace Current

/-- Data for a side-limit test. All laws are hypotheses of the assembler. -/
structure SideTarget (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  kappa : ℝ
  nL : ℕ
  nR : ℕ
  rhoL : Fin nL → ℝ
  rhoR : Fin nR → ℝ
  walls : MeasurableSpace Ω
  measure : @Measure Ω mΩ
  event : Set Ω
  curve : Ω → ℝ → ℂ
  marksL : Ω → Fin nL → ℝ
  marksR : Ω → Fin nR → ℝ
  domain : Ω → Set ℂ
  chart : Ω → ℂ → ℂ
  zeroField : Ω → DistOn upperHalfPlaneOpens
  harmonic : ℂ → ℝ

/-- Reference data for all relative stops of one test. The phase and offset
are common to all stops, as required by the native side-limit input. -/
structure SideReferences (Ω : Type*) where
  oldHull : ℚ≥0 → Ω → Set ℂ
  exterior : Ω → DistOn upperHalfPlaneOpens
  info : ℝ≥0 → CoverRef → MeasurableSpace Ω
  mean : ℝ≥0 → CoverRef → Ω → DistOn upperHalfPlaneOpens
  faces : ℝ≥0 → CoverRef → Ω → Set ℝ
  lift : ℝ≥0 → CoverRef → Ω → ℂ → ℝ
  height : ℝ≥0 → CoverRef → Ω → ℝ → ℝ
  branch : ℝ≥0 → CoverRef → Ω → ℝ → ℤ
  seed : Ω → ℂ
  phase : Ω → ℤ
  offset : ℝ

def SideTarget.baseChart {Ω : Type*} [MeasurableSpace Ω] (d : SideTarget Ω) : Ω → Chart :=
  pChart d.event d.domain d.chart

def SideTarget.jumps {Ω : Type*} [MeasurableSpace Ω] (d : SideTarget Ω)
    (q : ℝ≥0) : Ω → Set ℝ :=
  fun ω => forceJumpSet
    (fun i => geomLW (fun t ω => segDriver (d.curve ω) t) d.marksL i q ω - segDriver (d.curve ω) q)
    (fun j => geomRW (fun t ω => segDriver (d.curve ω) t) d.marksR j q ω - segDriver (d.curve ω) q)

/-- The unchanged native side-limit conclusion at a relative stop. -/
def SideTarget.Limit {Ω : Type*} [MeasurableSpace Ω] (d : SideTarget Ω)
    (n : Ω → ℤ) (a : ℝ) (q : ℝ≥0) : Prop :=
  PocketStopSideLimit d.kappa d.rhoL d.rhoR d.measure d.event d.curve d.marksL d.marksR
    (fun ω => shiftChart (d.baseChart ω) (n ω)) a d.zeroField d.harmonic
    (activeCompl d.event d.curve (fun ω => shiftChart (d.baseChart ω) (n ω)) q) q

end Current

open Current

/-- Side limits from raw laws, adjoining the exterior projection by the landed
EndLaws theorem. EndPieces supplies finite landings in either Jordan shape. -/
theorem current_sideLimits_of_raw_references {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (d : SideTarget Ω) (e : SideReferences Ω) (hull : ℝ≥0 → Ω → Set ℂ)
    [IsProbabilityMeasure d.measure]
    (hPrefix : ∀ q : ℝ≥0, locPrefixSigma d.walls d.event d.curve q ≤ mΩ)
    (hEvent : MeasurableSet[d.walls] d.event)
    (hDomainIn : ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[d.walls] {ω | ω ∈ d.event ∧ U ⊆ d.domain ω})
    (hDriven : ∀ ω ∈ d.event, IsDrivenCurve (d.curve ω))
    (hChart : IsPocketChartOn d.walls d.event d.domain d.chart d.baseChart)
    (hDomainMeasurable : ∀ z, MeasurableSet[d.walls] {ω | ω ∈ d.event ∧ z ∈ d.domain ω})
    (hOpen : ∀ ω ∈ d.event, IsOpen (d.domain ω))
    (hActive : ∀ (q : ℝ≥0) ω, ω ∈ d.event → (q : ℝ≥0∞) < capLife (d.curve ω) →
      activeDom d.event d.curve d.baseChart q ω = d.domain ω ∩ (H \ hull q ω))
    (hHullOpen : ∀ (q : ℝ≥0) ω, ω ∈ d.event → (q : ℝ≥0∞) < capLife (d.curve ω) → IsOpen (H \ hull q ω))
    (hZero : IsZeroBoundaryGFF upperHalfPlaneOpens d.zeroField d.measure)
    (hExterior : Measurable[germSigma (Sec7.Lemma725RefMarks.extA d.event d.domain) d.zeroField] e.exterior)
    (hUnion : ∀ q : ℝ≥0, PocketStopUnionLaw d.walls d.measure d.event d.curve d.domain (hull q) d.zeroField q)
    (hInfo : ∀ (q : ℝ≥0) i, e.info q i ≤ mΩ)
    (hReferenceUnion : ∀ (q : ℝ≥0) i, PocketStopUnionLaw (d.walls ⊔ e.info q i) d.measure d.event d.curve d.domain
      (fun ω => hull q ω ∪ referenceHull e.oldHull i ω) d.zeroField q)
    (hReferenceMarks : ∀ (q : ℝ≥0) i,
      MeasurableSpace.comap (activeCompl d.event d.curve d.baseChart q) hittingSigma ⊔
        MeasurableSpace.comap (referenceSet d.domain e.oldHull i) hittingSigma ≤
      locPrefixSigma ((d.walls ⊔ MeasurableSpace.comap e.exterior inferInstance) ⊔ e.info q i) d.event d.curve q)
    (hReferenceMeasurable : ∀ i, Measurable[mΩ, hittingSigma] (referenceSet d.domain e.oldHull i))
    (hReferenceLocal : ∀ i, IsLocalSet (referenceSet d.domain e.oldHull i) d.zeroField d.measure)
    (hReferenceUnbounded : ∀ i, ∀ᵐ ω ∂d.measure, ∀ z ∈ lowerUnion (referenceSet d.domain e.oldHull i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet d.domain e.oldHull i ω)) z))
    (hReferenceMean : ∀ (q : ℝ≥0) i, IsLocalSetMean (referenceSet d.domain e.oldHull i) d.zeroField d.measure (e.mean q i))
    (hJordan : ∀ ω ∈ d.event,
      (∃ pole : ℂ, IsBounded (d.domain ω) ∧ pole ∉ d.domain ω ∧
        Sec6.IsJordanCoord (d.domain ω) pole (e.seed ω) (d.chart ω)) ∨
      Sec6.IsJordanCoordInf (d.domain ω) (e.seed ω) (d.chart ω))
    (hClosure : ∀ ω ∈ d.event, closure (d.domain ω) ⊆ H ∪ {e.seed ω})
    (hRealCorner : ∀ q : ℝ≥0, ∀ᵐ ω ∂d.measure, ω ∈ d.event → (q : ℝ≥0∞) < capLife (d.curve ω) →
      e.seed ω ∉ H → ∀ ξ : ℝ, ξ ∉ d.jumps q ω → ∀ p : ℂ,
        Tendsto (relChart d.baseChart d.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ≠ e.seed ω)
    (hWallFaces : ∀ q : ℝ≥0, ∀ᵐ ω ∂d.measure, ω ∈ d.event → (q : ℝ≥0∞) < capLife (d.curve ω) →
      ∀ ξ : ℝ, ξ ∉ d.jumps q ω → ∀ p ∈ frontier (d.domain ω), p ∉ hull q ω →
        Tendsto (relChart d.baseChart d.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ j : Fin 2, ξ ∈ e.faces q (Sum.inl j) ω)
    (hOldHullSeparation : ∀ q : ℝ≥0, ∀ᵐ ω ∂d.measure, ω ∈ d.event → (q : ℝ≥0∞) < capLife (d.curve ω) →
      ∀ ξ : ℝ, ξ ∉ d.jumps q ω → ∀ p ∈ hull q ω,
        Tendsto (relChart d.baseChart d.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ (s : ℚ≥0) (r : ℝ), 0 < r ∧ ξ ∈ e.faces q (Sum.inr s) ω ∧
            e.oldHull s ω ⊆ hull q ω ∧ Disjoint (d.domain ω ∩ (hull q ω \ e.oldHull s ω)) (ball p r))
    (hOwnHeights : ∀ q : ℝ≥0, ReferenceHeightLimits (chiC d.kappa) d.measure d.event d.curve d.baseChart
      d.domain e.oldHull q d.harmonic (e.faces q) (e.mean q) (e.lift q) (e.height q))
    (hInheritedArguments : ∀ q : ℝ≥0, ReferenceLiftLimits d.measure d.event d.curve d.baseChart q
      (e.faces q) (e.lift q) (e.branch q))
    (hPhaseMeasurable : Measurable[d.walls] e.phase)
    (hPhaseZero : ∀ q : ℝ≥0, ∀ᵐ ω ∂d.measure, ω ∈ d.event → (q : ℝ≥0∞) < capLife (d.curve ω) →
      ∀ i ξ, ξ ∈ e.faces q i ω → e.height q i ω ξ + chiC d.kappa *
        (2 * Real.pi * e.branch q i ω ξ - 2 * Real.pi * e.phase ω) =
      forceBoundaryData d.kappa d.rhoL d.rhoR
        (fun i => geomLW (fun t ω => segDriver (d.curve ω) t) d.marksL i q ω - segDriver (d.curve ω) q)
        (fun j => geomRW (fun t ω => segDriver (d.curve ω) t) d.marksR j q ω - segDriver (d.curve ω) q) ξ - e.offset) :
    ∃ (n : Ω → ℤ) (a : ℝ), Measurable[d.walls] n ∧ ∀ q : ℝ≥0, d.Limit n a q := by
  refine ⟨e.phase, e.offset, hPhaseMeasurable, fun q => ?_⟩
  have hpieces := incidentReferenceCover_of_jordan_cases hDriven
    (fun ω hω => (hChart.1 ω hω).1) (fun ω hω => (hChart.1 ω hω).2.1)
    (fun ω hω => (hChart.1 ω hω).2.2.1) hJordan hClosure (hActive q) hOpen (hHullOpen q)
    (hRealCorner q) (hWallFaces q) (hOldHullSeparation q)
  exact (pocketStopSideLimit_pChart_of_raw_reference_laws (hPrefix q) hEvent hDomainIn hDriven
    hChart hDomainMeasurable hOpen (hActive q) (hHullOpen q) hZero hExterior (hUnion q)
    (hInfo q) (hReferenceUnion q) (hReferenceMarks q) hReferenceMeasurable hReferenceLocal
    hReferenceUnbounded (hReferenceMean q) hpieces (hOwnHeights q) (hInheritedArguments q)
    (hPhaseMeasurable.mono le_sup_left le_rfl) (hPhaseZero q)).2

end InteractingSLE.Wire
