/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInGeometry

/-!
# Pocket-word wiring with the geometric side inputs discharged

PROVE-POCKET-SIDEIN. Six of the eighteen named side inputs, and domain point
measurability, follow from `SideTest.Ready`. Reference data use the constructed
incoming corner. The remaining probabilistic, collar, height and phase inputs
are retained verbatim; this theorem does not claim the unconditional word law.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Sec7 LocalSets WangWu WholeField Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt

open Current

/-- The current pocket-word conclusion with eight geometric and measurability inputs
supplied internally. No original declaration is changed. The seed in the sole
real-corner premise is the actual closing corner of the two incoming walls. -/
theorem current_pocketWordEvolution_of_ready {Ω : Type} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (side : SideTest Ω → SideReferences Ω)
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω)
      (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean)
      d.measure)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver
      d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hX : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hζ : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ q t, Measurable fun ω => d.leftWall q ω t)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ q ω, Continuous (d.leftWall q ω))
    (hR0 : ∀ ω, d.rightWall ω 0 = 0)
    (hL0 : ∀ q ω, d.leftWall q ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => d.outerWall ω t)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
    (hηc : ∀ ω, ContinuousOn (d.curve ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → d.curve ω t ∈ Hbar)
    (hη0 : ∀ ω, d.curve ω 0 = 0)
    (hR : ∀ᵐ ω ∂d.measure, IsSimpleProper (d.rightWall ω) ∧ IsWallReverseVisit (d.rightWall ω)
      (d.curve ω) ∧ IsWallVisited (d.rightWall ω) (d.curve ω))
    (hβ : ∀ᵐ ω ∂d.measure, IsSimpleProper (d.outerWall ω) ∧ IsWallReverseVisit (d.outerWall ω)
      (d.curve ω) ∧ IsWallVisited (d.outerWall ω) (d.curve ω))
    (hLw : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsSimpleProper (d.leftWall q ω) ∧ IsWallReverseVisit
      (d.leftWall q ω) (d.curve ω) ∧
      d.leftWall q ω (StripSys.rt q) = d.outerWall ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂d.measure, ∀ t : ℝ, 0 < t → d.curve ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂d.measure, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ d.outerWall ω t ∉ range (d.rightWall ω))
    (htrace : ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) ∧
      Continuous (fun s : ℝ => d.driver s.toNNReal ω) ∧ d.driver 0 ω = 0)
    (hav : ∀ᵐ ω ∂d.measure, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (d.curve ω q) ∉ leftSideOf (range
      (d.outerWall ω)))
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω)
      (StripSys.rt q) →
      0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω) (StripSys.rt
        q))
        (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcL (d.rightWall ω)
          (d.leftWall q ω) (StripSys.rt q))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 1))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q
      ω) (StripSys.rt q) →
      rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖d.curve ω t‖) atTop atTop ∧ IsWallVisited (d.leftWall q ω) (d.curve ω) ∧
        Sec6.AttachmentConstancyInf (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω)
          (StripSys.rt q))
          (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcLInf (d.rightWall ω)
            (d.leftWall q ω) (StripSys.rt q))
          (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall q ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean)
      d.measure)
    (hlocL : ∀ q, Sec6.IsEntranceHistoryLocal (d.leftWall q) (centredField d.field d.originalMean)
      d.measure)
    (hu : InnerProductSpace.HarmonicOnNhd d.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, d.mean φ = ∫ z, d.harmonic z * φ z)
    (hSidePrefix : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d;
      ∀ q : ℝ≥0, locPrefixSigma target.walls target.event target.curve q ≤ mΩ)
    (hSideExterior : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      Measurable[germSigma (Sec7.Lemma725RefMarks.extA target.event target.domain)
        target.zeroField] refs.exterior)
    (hSideInfo : ∀ j : SideTest Ω, j.Ready d →
      let refs := side j;
      ∀ (q : ℝ≥0) i, refs.info q i ≤ mΩ)
    (hSideReferenceUnion : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i, PocketStopUnionLaw (target.walls ⊔ refs.info q i) target.measure target.event
        target.curve target.domain
      (fun ω => (j.hull d) q ω ∪ referenceHull refs.oldHull i ω) target.zeroField q)
    (hSideReferenceMarks : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i,
      MeasurableSpace.comap (activeCompl target.event target.curve target.baseChart q) hittingSigma
        ⊔
        MeasurableSpace.comap (referenceSet target.domain refs.oldHull i) hittingSigma ≤
      locPrefixSigma ((target.walls ⊔ MeasurableSpace.comap refs.exterior inferInstance) ⊔
        refs.info q i) target.event target.curve q)
    (hSideReferenceMeasurable : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, Measurable[mΩ, hittingSigma] (referenceSet target.domain refs.oldHull i))
    (hSideReferenceLocal : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, IsLocalSet (referenceSet target.domain refs.oldHull i) target.zeroField target.measure)
    (hSideReferenceUnbounded : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, ∀ᵐ ω ∂target.measure, ∀ z ∈ lowerUnion (referenceSet target.domain refs.oldHull i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet target.domain refs.oldHull i ω))
        z))
    (hSideReferenceMean : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i, IsLocalSetMean (referenceSet target.domain refs.oldHull i) target.zeroField
        target.measure (refs.mean q i))
    (hSideRealCorner : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      j.incomingSeed d ω ∉ H → ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p : ℂ,
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ≠
          j.incomingSeed d ω)
    (hSideWallFaces : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p ∈ frontier (target.domain ω), p ∉ (j.hull d) q ω →
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ j : Fin 2, ξ ∈ refs.faces q (Sum.inl j) ω)
    (hSideOldHullSeparation : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p ∈ (j.hull d) q ω,
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ (s : ℚ≥0) (r : ℝ), 0 < r ∧ ξ ∈ refs.faces q (Sum.inr s) ω ∧
            refs.oldHull s ω ⊆ (j.hull d) q ω ∧ Disjoint (target.domain ω ∩ ((j.hull d) q ω \
              refs.oldHull s ω)) (ball p r))
    (hSideOwnHeights : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ReferenceHeightLimits (chiC target.kappa) target.measure target.event target.curve
        target.baseChart
      target.domain refs.oldHull q target.harmonic (refs.faces q) (refs.mean q) (refs.lift q)
        (refs.height q))
    (hSideInheritedArguments : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ReferenceLiftLimits target.measure target.event target.curve target.baseChart q
      (refs.faces q) (refs.lift q) (refs.branch q))
    (hSidePhaseMeasurable : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      Measurable[target.walls] refs.phase)
    (hSidePhaseZero : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ i ξ, ξ ∈ refs.faces q i ω → refs.height q i ω ξ + chiC target.kappa *
        (2 * Real.pi * refs.branch q i ω ξ - 2 * Real.pi * refs.phase ω) =
      forceBoundaryData target.kappa target.rhoL target.rhoR
        (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver
          (target.curve ω) q)
        (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver
          (target.curve ω) q) ξ - refs.offset)
    : Sec7.Lemma725Ref.PocketWordEvolution.{0} i.kappa i.leftWeight i.rightWeight := by
  exact current_pocketWordEvolution i d
    (fun j => {side j with seed := j.incomingSeed d})
    (hT' := hT')
    (hTr := hTr)
    (hu₀ := hu₀)
    (hh := hh)
    (hC := hC)
    (hu₀' := hu₀')
    (hX := hX)
    (hζ := hζ)
    (hRm := hRm)
    (hLm := hLm)
    (hRc := hRc)
    (hLc := hLc)
    (hR0 := hR0)
    (hL0 := hL0)
    (hβm := hβm)
    (hηm := hηm)
    (hηc := hηc)
    (hηH := hηH)
    (hη0 := hη0)
    (hR := hR)
    (hβ := hβ)
    (hLw := hLw)
    (hnohit := hnohit)
    (hlate := hlate)
    (htrace := htrace)
    (hav := hav)
    (hattach := hattach)
    (hattachI := hattachI)
    (hdetR := hdetR)
    (hdetL := hdetL)
    (hlocR := hlocR)
    (hlocL := hlocL)
    (hu := hu)
    (hub := hub)
    (h𝔥 := h𝔥)
    (hSidePrefix := hSidePrefix)
    (hSideDomainIn := fun j hj => SideTest.measurableSet_domainIn hj hRc (hLc j.seed))
    (hSideChart := fun j hj => SideTest.isPocketChartOn hj hRc (hLc j.seed))
    (hSideDomainMeasurable := fun j hj => SideTest.measurableSet_domain hj hRc (hLc j.seed))
    (hSideOpen := fun j hj => SideTest.isOpen_domain hj)
    (hSideActive := fun j hj => SideTest.activeDom_eq hj hRc (hLc j.seed))
    (hSideHullOpen := fun j hj q ω hω _ => SideTest.isOpen_hull_compl hj q ω hω)
    (hSideExterior := hSideExterior)
    (hSideInfo := hSideInfo)
    (hSideReferenceUnion := hSideReferenceUnion)
    (hSideReferenceMarks := hSideReferenceMarks)
    (hSideReferenceMeasurable := hSideReferenceMeasurable)
    (hSideReferenceLocal := hSideReferenceLocal)
    (hSideReferenceUnbounded := hSideReferenceUnbounded)
    (hSideReferenceMean := hSideReferenceMean)
    (hSideJordan := fun j hj => SideTest.jordan_cases hj)
    (hSideClosure := fun j hj => SideTest.closure_domain hj)
    (hSideRealCorner := hSideRealCorner)
    (hSideWallFaces := hSideWallFaces)
    (hSideOldHullSeparation := hSideOldHullSeparation)
    (hSideOwnHeights := hSideOwnHeights)
    (hSideInheritedArguments := hSideInheritedArguments)
    (hSidePhaseMeasurable := hSidePhaseMeasurable)
    (hSidePhaseZero := hSidePhaseZero)

end InteractingSLE.Wire
