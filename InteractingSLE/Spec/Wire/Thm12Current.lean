/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12CurrentA2
import InteractingSLE.Spec.Wire.Thm12CurrentPocket
import InteractingSLE.Spec.Wire.Thm12CurrentStage
import InteractingSLE.WangWu.SeedTailLandingAssembly
import InteractingSLE.Spec.Sec7.R7PocketStop
import InteractingSLE.Spec.Sec7.Lemma725RefReglueStrip

/-!
# Current inputs of Theorems 1.2 and 1.3

The current statements discharge the proved four-chamber theorem. The expanded
statement uses the R70 reference couplings, proved Part 1 crosscuts, Parts 2/3's
latest reductions, the finite-crosscut detour, and the per-q marked-stop and
raw side-reference assemblies. The determination reference is supplied by the
named strip-pocket-marks input. Every remaining law is a named hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire

/-- Theorem 1.2 with the proved four-chamber joint theorem supplied. -/
theorem theorem12Statement_current
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) : Exist.Theorem12Statement.{u} :=
  theorem12Statement_of_A2 hA2 hA2' h47 hfirst WangWu.SeedTail.chamber4JointStatement
    hR7 hPW href725

/-- Theorem 1.3 with the proved four-chamber joint theorem supplied. -/
theorem theorem13Statement_current
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ) :
    Exist.Theorem13Statement.{u} :=
  theorem13Statement_of_A2 h47 h51 WangWu.SeedTail.chamber4JointStatement hR7 hPW hA2 hA2'


open Current
open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open WangWu (negInv)
open Sec7 LocalSets WangWu WholeField Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt

/-- Theorem 1.2 with the latest reductions composed. The object families store
data only. The side hypotheses quantify only tests already required by the
native per-q assembly. The strip-marks premise is the existing named source
input; in particular its Proposition 5.13 conclusion remains a mathematical input
until the source experiments are supplied (see `current_prop513_path_of_clearance_reverseVisit_candExp`). -/
theorem theorem12Statement_expanded
    (hA1 : ∀ κ : ℝ, ZhanGT4.A1Dual.A1DualCouplingG3RefStatement κ)
    (hTipSep : ∀ κ : ℝ, ZhanGT4.A2Part2.A2TipSepG3Statement.{0} κ)
    (hImage : ∀ κ : ℝ, ZhanGT4.A2X.P3.ImageDichotomyG3Statement.{0} κ)
    (hPair : ∀ κ : ℝ, ZhanGT4.A2X.P3.PairContactG3Statement.{0} κ)
    (hA1Eight : ∀ κ : ℝ, ZhanGT4.A1Dual.A1DualCouplingEightRefStatement κ)
    (hTipSepEight : ∀ κ : ℝ, ZhanGT4.A2Part2.A2TipSepEightStatement.{0} κ)
    (hImageEight : ∀ κ : ℝ, ZhanGT4.A2X.P3.ImageDichotomyEightStatement.{0} κ)
    (hPairEight : ∀ κ : ℝ, ZhanGT4.A2X.P3.PairContactEightStatement.{0} κ)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hFiniteBypass : Sec5.Prop51HTopo.FiniteWesternCrosscutBypassStatement)
    (hEast : Sec5.Prop51I.FwdPostContactEastSideQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (hR7Pocket : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 ≤ max rL rR → Sec7.R7Pocket.R7PocketStopStatement.{0} κ rL rR
        fun w ζ => ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧
          (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop))
    (hStripMarks : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 →
      -2 < rR → rR < κ / 2 - 4 → Sec7.Lemma725RefMarks.StripPocketMarksInput.{u} κ rL rR)
    (Ω : BothLow → Type) [mΩ : ∀ i, MeasurableSpace (Ω i)]
    [hWordBorel : ∀ i, StandardBorelSpace (Ω i)]
    (word : ∀ i, WordObjects (Ω i)) [hWordProbability : ∀ i, IsProbabilityMeasure (word i).measure]
    (side : ∀ i, SideTest (Ω i) → SideReferences (Ω i))
    (hWordTransport : ∀ i, let d := word i;
      ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω) (d.chartField ω))
    (hWordTranslate : ∀ i, let d := word i;
      ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hWordOriginalHarmonic : ∀ i, let d := word i;
      InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hWordOriginalGFF : ∀ i, let d := word i;
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hWordCoupling : ∀ i, let d := word i;
      IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hWordBoundaryMean : ∀ i, let d := word i;
      IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean)
    (hWordKilledMeasurable : ∀ i, let d := word i;
      IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hWordLifetime : ∀ i, let d := word i;
      ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hWordRightMeasurable : ∀ i, let d := word i;
      ∀ t, Measurable fun ω => d.rightWall ω t)
    (hWordLeftMeasurable : ∀ i, let d := word i;
      ∀ q t, Measurable fun ω => d.leftWall q ω t)
    (hWordRightContinuous : ∀ i, let d := word i;
      ∀ ω, Continuous (d.rightWall ω))
    (hWordLeftContinuous : ∀ i, let d := word i;
      ∀ q ω, Continuous (d.leftWall q ω))
    (hWordRightSeed : ∀ i, let d := word i;
      ∀ ω, d.rightWall ω 0 = 0)
    (hWordLeftSeed : ∀ i, let d := word i;
      ∀ q ω, d.leftWall q ω 0 = 0)
    (hWordOuterMeasurable : ∀ i, let d := word i;
      ∀ t, Measurable fun ω => d.outerWall ω t)
    (hWordCurveMeasurable : ∀ i, let d := word i;
      ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
    (hWordCurveContinuous : ∀ i, let d := word i;
      ∀ ω, ContinuousOn (d.curve ω) (Ici 0))
    (hWordCurveHbar : ∀ i, let d := word i;
      ∀ ω, ∀ t : ℝ, 0 ≤ t → d.curve ω t ∈ Hbar)
    (hWordCurveSeed : ∀ i, let d := word i;
      ∀ ω, d.curve ω 0 = 0)
    (hWordRightGeometry : ∀ i, let d := word i;
      ∀ᵐ ω ∂d.measure, IsSimpleProper (d.rightWall ω) ∧ IsWallReverseVisit (d.rightWall ω) (d.curve ω) ∧ IsWallVisited (d.rightWall ω) (d.curve ω))
    (hWordOuterGeometry : ∀ i, let d := word i;
      ∀ᵐ ω ∂d.measure, IsSimpleProper (d.outerWall ω) ∧ IsWallReverseVisit (d.outerWall ω) (d.curve ω) ∧ IsWallVisited (d.outerWall ω) (d.curve ω))
    (hWordLeftGeometry : ∀ i, let d := word i;
      ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsSimpleProper (d.leftWall q ω) ∧ IsWallReverseVisit (d.leftWall q ω) (d.curve ω) ∧
      d.leftWall q ω (StripSys.rt q) = d.outerWall ω (StripSys.rt q))
    (hWordNoHit : ∀ i, let d := word i;
      ∀ᵐ ω ∂d.measure, ∀ t : ℝ, 0 < t → d.curve ω t ≠ 0)
    (hWordLate : ∀ i, let d := word i;
      ∀ᵐ ω ∂d.measure, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ d.outerWall ω t ∉ range (d.rightWall ω))
    (hWordTrace : ∀ i, let d := word i;
      ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) ∧
      Continuous (fun s : ℝ => d.driver s.toNNReal ω) ∧ d.driver 0 ω = 0)
    (hWordAvoidance : ∀ i, let d := word i;
      ∀ᵐ ω ∂d.measure, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (d.curve ω q) ∉ leftSideOf (range (d.outerWall ω)))
    (hWordAttachment : ∀ i, let d := word i;
      ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
        (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcL (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 1))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
    (hWordAttachmentInf : ∀ i, let d := word i;
      ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖d.curve ω t‖) atTop atTop ∧ IsWallVisited (d.leftWall q ω) (d.curve ω) ∧
        Sec6.AttachmentConstancyInf (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
          (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcLInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
          (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
    (hWordRightDetermination : ∀ i, let d := word i;
      ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hWordLeftDetermination : ∀ i, let d := word i;
      ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall q ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hWordRightLocal : ∀ i, let d := word i;
      Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
    (hWordLeftLocal : ∀ i, let d := word i;
      ∀ q, Sec6.IsEntranceHistoryLocal (d.leftWall q) (centredField d.field d.originalMean) d.measure)
    (hWordHarmonic : ∀ i, let d := word i;
      InnerProductSpace.HarmonicOnNhd d.harmonic H)
    (hWordBounded : ∀ i, let d := word i;
      ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
    (hWordMean : ∀ i, let d := word i;
      ∀ φ : TestOn upperHalfPlaneOpens, d.mean φ = ∫ z, d.harmonic z * φ z)
    (hSidePrefix : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ q : ℝ≥0, locPrefixSigma target.walls target.event target.curve q ≤ (mΩ index))
    (hSideDomainIn : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[target.walls] {ω | ω ∈ target.event ∧ U ⊆ target.domain ω})
    (hSideChart : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      IsPocketChartOn target.walls target.event target.domain target.chart target.baseChart)
    (hSideDomainMeasurable : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ z, MeasurableSet[target.walls] {ω | ω ∈ target.event ∧ z ∈ target.domain ω})
    (hSideOpen : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ ω ∈ target.event, IsOpen (target.domain ω))
    (hSideActive : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ (q : ℝ≥0) ω, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      activeDom target.event target.curve target.baseChart q ω = target.domain ω ∩ (H \ (j.hull d) q ω))
    (hSideHullOpen : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ (q : ℝ≥0) ω, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) → IsOpen (H \ (j.hull d) q ω))
    (hSideExterior : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      Measurable[germSigma (Sec7.Lemma725RefMarks.extA target.event target.domain) target.zeroField] refs.exterior)
    (hSideInfo : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ (q : ℝ≥0) i, refs.info q i ≤ (mΩ index))
    (hSideReferenceUnion : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ (q : ℝ≥0) i, PocketStopUnionLaw (target.walls ⊔ refs.info q i) target.measure target.event target.curve target.domain
      (fun ω => (j.hull d) q ω ∪ referenceHull refs.oldHull i ω) target.zeroField q)
    (hSideReferenceMarks : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ (q : ℝ≥0) i,
      MeasurableSpace.comap (activeCompl target.event target.curve target.baseChart q) hittingSigma ⊔
        MeasurableSpace.comap (referenceSet target.domain refs.oldHull i) hittingSigma ≤
      locPrefixSigma ((target.walls ⊔ MeasurableSpace.comap refs.exterior inferInstance) ⊔ refs.info q i) target.event target.curve q)
    (hSideReferenceMeasurable : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ i, Measurable[(mΩ index), hittingSigma] (referenceSet target.domain refs.oldHull i))
    (hSideReferenceLocal : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ i, IsLocalSet (referenceSet target.domain refs.oldHull i) target.zeroField target.measure)
    (hSideReferenceUnbounded : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ i, ∀ᵐ ω ∂target.measure, ∀ z ∈ lowerUnion (referenceSet target.domain refs.oldHull i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet target.domain refs.oldHull i ω)) z))
    (hSideReferenceMean : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ (q : ℝ≥0) i, IsLocalSetMean (referenceSet target.domain refs.oldHull i) target.zeroField target.measure (refs.mean q i))
    (hSideJordan : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ ω ∈ target.event,
      (∃ pole : ℂ, IsBounded (target.domain ω) ∧ pole ∉ target.domain ω ∧
        Sec6.IsJordanCoord (target.domain ω) pole (refs.seed ω) (target.chart ω)) ∨
      Sec6.IsJordanCoordInf (target.domain ω) (refs.seed ω) (target.chart ω))
    (hSideClosure : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ ω ∈ target.event, closure (target.domain ω) ⊆ H ∪ {refs.seed ω})
    (hSideRealCorner : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      refs.seed ω ∉ H → ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p : ℂ,
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ≠ refs.seed ω)
    (hSideWallFaces : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p ∈ frontier (target.domain ω), p ∉ (j.hull d) q ω →
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ j : Fin 2, ξ ∈ refs.faces q (Sum.inl j) ω)
    (hSideOldHullSeparation : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p ∈ (j.hull d) q ω,
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ (s : ℚ≥0) (r : ℝ), 0 < r ∧ ξ ∈ refs.faces q (Sum.inr s) ω ∧
            refs.oldHull s ω ⊆ (j.hull d) q ω ∧ Disjoint (target.domain ω ∩ ((j.hull d) q ω \ refs.oldHull s ω)) (ball p r))
    (hSideOwnHeights : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ q : ℝ≥0, ReferenceHeightLimits (chiC target.kappa) target.measure target.event target.curve target.baseChart
      target.domain refs.oldHull q target.harmonic (refs.faces q) (refs.mean q) (refs.lift q) (refs.height q))
    (hSideInheritedArguments : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ q : ℝ≥0, ReferenceLiftLimits target.measure target.event target.curve target.baseChart q
      (refs.faces q) (refs.lift q) (refs.branch q))
    (hSidePhaseMeasurable : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      Measurable[target.walls] refs.phase)
    (hSidePhaseZero : ∀ index (j : SideTest (Ω index)), j.Ready (word index) →
      let d := word index; let target := j.target index d; let refs := side index j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ i ξ, ξ ∈ refs.faces q i ω → refs.height q i ω ξ + chiC target.kappa *
        (2 * Real.pi * refs.branch q i ω ξ - 2 * Real.pi * refs.phase ω) =
      forceBoundaryData target.kappa target.rhoL target.rhoR
        (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve ω) q)
        (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve ω) q) ξ - refs.offset)
    : Exist.Theorem12Statement.{u} := by
  have hA2 := current_fourForceCrosscutG3LifeStatement hA1 hTipSep hImage hPair
  have hA2' := current_threeForceCrosscutEightStatement hA1Eight hTipSepEight hImageEight hPairEight
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have hfirst := current_cfFirstContactQStatement hA hFiniteBypass hEast
  have hR7 := Sec7.R7Pocket.r7ReferenceStatement_of_r7PocketStop hR7Pocket
  have href725 := Sec7.Lemma725RefMarks.lemma725DetReferenceStatement_of_stripPocketMarks hStripMarks
  have hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR := by
    intro κ hκ rL rR hL hLd hR hRd
    let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
    exact current_pocketWordEvolution i (word i) (side i)
      (hWordTransport i) (hWordTranslate i) (hWordOriginalHarmonic i)
      (hWordOriginalGFF i) (hWordCoupling i) (hWordBoundaryMean i)
      (hWordKilledMeasurable i) (hWordLifetime i) (hWordRightMeasurable i)
      (hWordLeftMeasurable i) (hWordRightContinuous i) (hWordLeftContinuous i)
      (hWordRightSeed i) (hWordLeftSeed i) (hWordOuterMeasurable i)
      (hWordCurveMeasurable i) (hWordCurveContinuous i) (hWordCurveHbar i)
      (hWordCurveSeed i) (hWordRightGeometry i) (hWordOuterGeometry i)
      (hWordLeftGeometry i) (hWordNoHit i) (hWordLate i)
      (hWordTrace i) (hWordAvoidance i) (hWordAttachment i)
      (hWordAttachmentInf i) (hWordRightDetermination i) (hWordLeftDetermination i)
      (hWordRightLocal i) (hWordLeftLocal i) (hWordHarmonic i)
      (hWordBounded i) (hWordMean i) (hSidePrefix i)
      (hSideDomainIn i) (hSideChart i) (hSideDomainMeasurable i)
      (hSideOpen i) (hSideActive i) (hSideHullOpen i)
      (hSideExterior i) (hSideInfo i) (hSideReferenceUnion i)
      (hSideReferenceMarks i) (hSideReferenceMeasurable i) (hSideReferenceLocal i)
      (hSideReferenceUnbounded i) (hSideReferenceMean i) (hSideJordan i)
      (hSideClosure i) (hSideRealCorner i) (hSideWallFaces i)
      (hSideOldHullSeparation i) (hSideOwnHeights i) (hSideInheritedArguments i)
      (hSidePhaseMeasurable i) (hSidePhaseZero i)
  exact theorem12Statement_current hA2 hA2' h47 hfirst hR7 hPW href725

end InteractingSLE.Wire
