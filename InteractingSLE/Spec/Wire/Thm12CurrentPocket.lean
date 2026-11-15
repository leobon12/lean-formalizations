/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12CurrentSide
import InteractingSLE.Spec.Sec7.PocketWordPerQSide

/-! # Per-q pocket words with the raw side-reference obligations exposed -/

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

namespace Current

/-- The source parameter range of the both-low pocket references. -/
structure BothLow where
  kappa : ℝ
  leftWeight : ℝ
  rightWeight : ℝ
  kappa_gt_four : 4 < kappa
  left_gt : -2 < leftWeight
  left_lt : leftWeight < kappa / 2 - 4
  right_gt : -2 < rightWeight
  right_lt : rightWeight < kappa / 2 - 4

/-- Source objects for one strip coupling. All their laws are separate inputs. -/
structure WordObjects (Ω : Type) [mΩ : MeasurableSpace Ω] where
  measure : Measure Ω
  nL : ℕ
  nR : ℕ
  xL : Fin nL → ℝ
  xR : Fin nR → ℝ
  rhoL : Fin nL → ℝ
  rhoR : Fin nR → ℝ
  field : Ω → DistOn upperHalfPlaneOpens
  chartField : Ω → DistOn upperHalfPlaneOpens
  translatedField : Ω → DistOn upperHalfPlaneOpens
  scale : ℝ
  chartConstant : ℝ
  translateConstant : ℝ
  originalMean : ℂ → ℝ
  filtration : Filtration ℝ≥0 mΩ
  driver : ℝ≥0 → Ω → ℝ
  forceL : Fin nL → ℝ≥0 → Ω → ℝ
  forceR : Fin nR → ℝ≥0 → Ω → ℝ
  brownian : ℝ≥0 → Ω → ℝ
  lifetime : Ω → ℝ≥0∞
  coupledMean : ℂ → ℝ
  rightWall : Ω → ℝ≥0 → ℂ
  outerWall : Ω → ℝ≥0 → ℂ
  leftWall : ℚ → Ω → ℝ≥0 → ℂ
  curve : Ω → ℝ → ℂ
  mean : DistOn upperHalfPlaneOpens
  harmonic : ℂ → ℝ

/-- One of the four shape tests in the native per-q side-limit input. -/
structure SideTest (Ω : Type) where
  seed : ℚ
  outerEvent : Set Ω
  event : Set Ω
  chart : Ω → ℂ → ℂ
  infinite : Bool
  twoLeft : Bool

/-- The side target has exactly the selected pair's walls information. -/
def SideTest.target {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω)
    (i : BothLow) (d : WordObjects Ω) : SideTarget Ω :=
  let base : SideTarget Ω := {
    kappa := 16 / (16 / i.kappa)
    nL := 1
    nR := 2
    rhoL := wordL1 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight)
    rhoR := wordR2 (16 / i.kappa) (rs136Theta2 (16 / i.kappa) i.rightWeight)
    walls := wallsSigma d.measure d.rightWall (d.leftWall j.seed)
    measure := d.measure
    event := j.event
    curve := if j.infinite then travAllInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart
      else travAll d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed) d.curve j.chart
    marksL := marksL1All
    marksR := marksRAll (d.leftWall j.seed) (StripSys.rt j.seed) j.chart
    domain := fun ω => cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)
    chart := j.chart
    zeroField := centredField d.translatedField d.coupledMean
    harmonic := d.harmonic }
  if j.twoLeft then { base with
    nL := 2
    rhoL := wordL2 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight)
    marksL := marksL2All d.rightWall j.chart } else base

/-- The actual filled hull at the consumer's right stop T(q). -/
def SideTest.hull {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω)
    (d : WordObjects Ω) (q : ℝ≥0) : Ω → Set ℂ :=
  if j.infinite then stopHullInf d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed)
    (fun ω (s : ℝ) => d.driver s.toNNReal ω) d.curve j.chart q
  else stopHull d.rightWall (d.leftWall j.seed) (StripSys.rt j.seed)
    (fun ω (s : ℝ) => d.driver s.toNNReal ω) d.curve j.chart q

/-- Preconditions already quantified by the native per-q assembly.
This predicate contains no side limit, local-set law, height law or phase conclusion. -/
def SideTest.Ready {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω) (d : WordObjects Ω) : Prop :=
  let R := d.rightWall
  let L := d.leftWall j.seed
  let r := StripSys.rt j.seed
  let G := j.outerEvent
  0 < j.seed ∧ MeasurableSet[wallsSigma d.measure R L] G ∧ 0 < d.measure G ∧
    (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r ∧ discTime 1 < rightHi (R ω) (L ω) r) ∧
    (∀ ω ∈ G, d.lifetime ω = ⊤) ∧
    (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r →
      IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) ∧
    (∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 →
      IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) ∧
    MeasurableSet[wallsSigma d.measure R L] j.event ∧
    j.event ⊆ (if j.infinite then {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r}
      else {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r}) ∧
    0 < d.measure j.event ∧
    (if j.infinite then ∀ ω ∈ j.event, IsCfJordanInf (R ω) (L ω) r (j.chart ω)
      else ∀ ω ∈ j.event, IsCfJordan (R ω) (L ω) r (j.chart ω)) ∧
    (if j.infinite then @IsPointMeasurableInf Ω (wallsSigma d.measure R L) R L r
        {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} j.chart
      else @IsPointMeasurable Ω (wallsSigma d.measure R L) R L r
        {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} j.chart) ∧
    (if j.twoLeft then ∀ ω ∈ j.event, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)
      else ∀ ω ∈ j.event, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r))

end Current

open Current

/-- The marked-stop and exterior-enlargement conclusions are supplied by the
landed per-q and SideEnd assemblies. Every remaining law is a separate argument. -/
theorem current_pocketWordEvolution {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (side : SideTest Ω → SideReferences Ω)
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean)
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
    (hR : ∀ᵐ ω ∂d.measure, IsSimpleProper (d.rightWall ω) ∧ IsWallReverseVisit (d.rightWall ω) (d.curve ω) ∧ IsWallVisited (d.rightWall ω) (d.curve ω))
    (hβ : ∀ᵐ ω ∂d.measure, IsSimpleProper (d.outerWall ω) ∧ IsWallReverseVisit (d.outerWall ω) (d.curve ω) ∧ IsWallVisited (d.outerWall ω) (d.curve ω))
    (hLw : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsSimpleProper (d.leftWall q ω) ∧ IsWallReverseVisit (d.leftWall q ω) (d.curve ω) ∧
      d.leftWall q ω (StripSys.rt q) = d.outerWall ω (StripSys.rt q))
    (hnohit : ∀ᵐ ω ∂d.measure, ∀ t : ℝ, 0 < t → d.curve ω t ≠ 0)
    (hlate : ∀ᵐ ω ∂d.measure, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ d.outerWall ω t ∉ range (d.rightWall ω))
    (htrace : ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) ∧
      Continuous (fun s : ℝ => d.driver s.toNNReal ω) ∧ d.driver 0 ω = 0)
    (hav : ∀ᵐ ω ∂d.measure, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (d.curve ω q) ∉ leftSideOf (range (d.outerWall ω)))
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
        (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcL (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 1))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖d.curve ω t‖) atTop atTop ∧ IsWallVisited (d.leftWall q ω) (d.curve ω) ∧
        Sec6.AttachmentConstancyInf (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
          (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcLInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
          (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall q ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
    (hlocL : ∀ q, Sec6.IsEntranceHistoryLocal (d.leftWall q) (centredField d.field d.originalMean) d.measure)
    (hu : InnerProductSpace.HarmonicOnNhd d.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, d.mean φ = ∫ z, d.harmonic z * φ z)
    (hSidePrefix : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, locPrefixSigma target.walls target.event target.curve q ≤ mΩ)
    (hSideDomainIn : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ U : Set ℂ, IsOpen U → U ⊆ H →
      MeasurableSet[target.walls] {ω | ω ∈ target.event ∧ U ⊆ target.domain ω})
    (hSideChart : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      IsPocketChartOn target.walls target.event target.domain target.chart target.baseChart)
    (hSideDomainMeasurable : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ z, MeasurableSet[target.walls] {ω | ω ∈ target.event ∧ z ∈ target.domain ω})
    (hSideOpen : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ ω ∈ target.event, IsOpen (target.domain ω))
    (hSideActive : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) ω, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      activeDom target.event target.curve target.baseChart q ω = target.domain ω ∩ (H \ (j.hull d) q ω))
    (hSideHullOpen : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) ω, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) → IsOpen (H \ (j.hull d) q ω))
    (hSideExterior : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      Measurable[germSigma (Sec7.Lemma725RefMarks.extA target.event target.domain) target.zeroField] refs.exterior)
    (hSideInfo : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i, refs.info q i ≤ mΩ)
    (hSideReferenceUnion : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i, PocketStopUnionLaw (target.walls ⊔ refs.info q i) target.measure target.event target.curve target.domain
      (fun ω => (j.hull d) q ω ∪ referenceHull refs.oldHull i ω) target.zeroField q)
    (hSideReferenceMarks : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i,
      MeasurableSpace.comap (activeCompl target.event target.curve target.baseChart q) hittingSigma ⊔
        MeasurableSpace.comap (referenceSet target.domain refs.oldHull i) hittingSigma ≤
      locPrefixSigma ((target.walls ⊔ MeasurableSpace.comap refs.exterior inferInstance) ⊔ refs.info q i) target.event target.curve q)
    (hSideReferenceMeasurable : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, Measurable[mΩ, hittingSigma] (referenceSet target.domain refs.oldHull i))
    (hSideReferenceLocal : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, IsLocalSet (referenceSet target.domain refs.oldHull i) target.zeroField target.measure)
    (hSideReferenceUnbounded : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, ∀ᵐ ω ∂target.measure, ∀ z ∈ lowerUnion (referenceSet target.domain refs.oldHull i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet target.domain refs.oldHull i ω)) z))
    (hSideReferenceMean : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i, IsLocalSetMean (referenceSet target.domain refs.oldHull i) target.zeroField target.measure (refs.mean q i))
    (hSideJordan : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ ω ∈ target.event,
      (∃ pole : ℂ, IsBounded (target.domain ω) ∧ pole ∉ target.domain ω ∧
        Sec6.IsJordanCoord (target.domain ω) pole (refs.seed ω) (target.chart ω)) ∨
      Sec6.IsJordanCoordInf (target.domain ω) (refs.seed ω) (target.chart ω))
    (hSideClosure : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ ω ∈ target.event, closure (target.domain ω) ⊆ H ∪ {refs.seed ω})
    (hSideRealCorner : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      refs.seed ω ∉ H → ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p : ℂ,
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ≠ refs.seed ω)
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
            refs.oldHull s ω ⊆ (j.hull d) q ω ∧ Disjoint (target.domain ω ∩ ((j.hull d) q ω \ refs.oldHull s ω)) (ball p r))
    (hSideOwnHeights : ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ReferenceHeightLimits (chiC target.kappa) target.measure target.event target.curve target.baseChart
      target.domain refs.oldHull q target.harmonic (refs.faces q) (refs.mean q) (refs.lift q) (refs.height q))
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
        (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve ω) q)
        (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve ω) q) ξ - refs.offset)
    : Sec7.Lemma725Ref.PocketWordEvolution.{0} i.kappa i.leftWeight i.rightWeight := by
  apply pocketWordEvolution_of_stripPocket_sideLimit_perQ i.kappa_gt_four i.left_gt i.left_lt i.right_gt i.right_lt
    hT' hTr hu₀ hh hC hu₀' hX hζ hRm hLm hRc hLc hR0 hL0 hβm hηm hηc hηH hη0
    hR hβ hLw hnohit hlate htrace hav hattach hattachI hdetR hdetL hlocR hlocL d.mean hu hub h𝔥
  intro q hq G hG hPG hconf hζG hcfg hcfgI
  have hRm' := fun t => measurable_right_wallsSigma (P := d.measure) hRc (hLc q) t
  have hLm' := fun t => measurable_left_wallsSigma (P := d.measure) hRc (hLc q) t
  have hGp : MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)]
      {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma d.measure d.rightWall (d.leftWall q))
      hRm' hLm' hG (fun ω hω => (hconf ω hω).1)).1
  have hG0 : MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)]
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)} := by
    convert hG.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgB := fun ω (hω : ω ∈ {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)}) =>
    hcfg ω hω.1 hω.2
  have hcfgInf := fun ω (hω : ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)}) =>
    hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).1.changeCorner_props.1.1))
  constructor
  · intro A hA hAG hPA ψ hJordan hPoint
    constructor
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, false, true⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      letI : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfg ω (hAG hω).1 (hAG hω).2).isDrivenCurve (hJordan ω hω)).1
      have hUnion : ∀ s : ℝ≥0, PocketStopUnionLaw (j.target i d).walls d.measure A
        (j.target i d).curve (j.target i d).domain (j.hull d s) (centredField d.translatedField d.coupledMean) s := by
        intro s
        exact pocketStopUnionLaw_stopHull_strip_marked hT' hTr hu₀ hh hC (by have := i.kappa_gt_four; linarith only [this]) hu₀' hX hζ
          hRc (hLc q) hR0 (hL0 q) hRm (hLm q) hdetR (hdetL q) hlocR (hlocL q)
          (wallsSigma_le hRm (hLm q)) (wallsSigma_le_drivingFiltration hX d.rightWall (d.leftWall q)) hRm' hLm'
          hGp hcfgB hA hAG (fun ω hω => hζG ω (hAG hω).1) hJordan hPoint s (hSidePrefix j hj s)
      exact current_sideLimits_of_raw_references (j.target i d) (side j) (j.hull d)
        (hSidePrefix j hj) hA (hSideDomainIn j hj)
        hDriven (hSideChart j hj) (hSideDomainMeasurable j hj)
        (hSideOpen j hj) (hSideActive j hj) (hSideHullOpen j hj)
        (isZeroBoundaryGFF_centredField hC hu₀') (hSideExterior j hj) hUnion
        (hSideInfo j hj) (hSideReferenceUnion j hj) (hSideReferenceMarks j hj)
        (hSideReferenceMeasurable j hj) (hSideReferenceLocal j hj) (hSideReferenceUnbounded j hj)
        (hSideReferenceMean j hj) (hSideJordan j hj) (hSideClosure j hj)
        (hSideRealCorner j hj) (hSideWallFaces j hj) (hSideOldHullSeparation j hj)
        (hSideOwnHeights j hj) (hSideInheritedArguments j hj) (hSidePhaseMeasurable j hj)
        (hSidePhaseZero j hj)
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, false, false⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      letI : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfg ω (hAG hω).1 (hAG hω).2).isDrivenCurve (hJordan ω hω)).1
      have hUnion : ∀ s : ℝ≥0, PocketStopUnionLaw (j.target i d).walls d.measure A
        (j.target i d).curve (j.target i d).domain (j.hull d s) (centredField d.translatedField d.coupledMean) s := by
        intro s
        exact pocketStopUnionLaw_stopHull_strip_marked hT' hTr hu₀ hh hC (by have := i.kappa_gt_four; linarith only [this]) hu₀' hX hζ
          hRc (hLc q) hR0 (hL0 q) hRm (hLm q) hdetR (hdetL q) hlocR (hlocL q)
          (wallsSigma_le hRm (hLm q)) (wallsSigma_le_drivingFiltration hX d.rightWall (d.leftWall q)) hRm' hLm'
          hGp hcfgB hA hAG (fun ω hω => hζG ω (hAG hω).1) hJordan hPoint s (hSidePrefix j hj s)
      exact current_sideLimits_of_raw_references (j.target i d) (side j) (j.hull d)
        (hSidePrefix j hj) hA (hSideDomainIn j hj)
        hDriven (hSideChart j hj) (hSideDomainMeasurable j hj)
        (hSideOpen j hj) (hSideActive j hj) (hSideHullOpen j hj)
        (isZeroBoundaryGFF_centredField hC hu₀') (hSideExterior j hj) hUnion
        (hSideInfo j hj) (hSideReferenceUnion j hj) (hSideReferenceMarks j hj)
        (hSideReferenceMeasurable j hj) (hSideReferenceLocal j hj) (hSideReferenceUnbounded j hj)
        (hSideReferenceMean j hj) (hSideJordan j hj) (hSideClosure j hj)
        (hSideRealCorner j hj) (hSideWallFaces j hj) (hSideOldHullSeparation j hj)
        (hSideOwnHeights j hj) (hSideInheritedArguments j hj) (hSidePhaseMeasurable j hj)
        (hSidePhaseZero j hj)
  · intro A hA hAG hPA ψ hJordan hPoint
    constructor
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, true, true⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      letI : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfgI ω (hAG hω).1 (le_antisymm (not_lt.1 (hAG hω).2) ((hconf ω (hAG hω).1).1.changeCorner_props.1.1))).isDrivenCurve (hJordan ω hω)).1
      have hUnion : ∀ s : ℝ≥0, PocketStopUnionLaw (j.target i d).walls d.measure A
        (j.target i d).curve (j.target i d).domain (j.hull d s) (centredField d.translatedField d.coupledMean) s := by
        intro s
        exact pocketStopUnionLaw_stopHullInf_strip_marked hT' hTr hu₀ hh hC (by have := i.kappa_gt_four; linarith only [this]) hu₀' hX hζ
          hRc (hLc q) hR0 (hL0 q) hRm (hLm q) hdetR (hdetL q) hlocR (hlocL q)
          (wallsSigma_le hRm (hLm q)) (wallsSigma_le_drivingFiltration hX d.rightWall (d.leftWall q)) hRm' hLm'
          hG0 hcfgInf hA hAG (fun ω hω => hζG ω (hAG hω).1) hJordan hPoint s (hSidePrefix j hj s)
      exact current_sideLimits_of_raw_references (j.target i d) (side j) (j.hull d)
        (hSidePrefix j hj) hA (hSideDomainIn j hj)
        hDriven (hSideChart j hj) (hSideDomainMeasurable j hj)
        (hSideOpen j hj) (hSideActive j hj) (hSideHullOpen j hj)
        (isZeroBoundaryGFF_centredField hC hu₀') (hSideExterior j hj) hUnion
        (hSideInfo j hj) (hSideReferenceUnion j hj) (hSideReferenceMarks j hj)
        (hSideReferenceMeasurable j hj) (hSideReferenceLocal j hj) (hSideReferenceUnbounded j hj)
        (hSideReferenceMean j hj) (hSideJordan j hj) (hSideClosure j hj)
        (hSideRealCorner j hj) (hSideWallFaces j hj) (hSideOldHullSeparation j hj)
        (hSideOwnHeights j hj) (hSideInheritedArguments j hj) (hSidePhaseMeasurable j hj)
        (hSidePhaseZero j hj)
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, true, false⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      letI : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfgI ω (hAG hω).1 (le_antisymm (not_lt.1 (hAG hω).2) ((hconf ω (hAG hω).1).1.changeCorner_props.1.1))).isDrivenCurve (hJordan ω hω)).1
      have hUnion : ∀ s : ℝ≥0, PocketStopUnionLaw (j.target i d).walls d.measure A
        (j.target i d).curve (j.target i d).domain (j.hull d s) (centredField d.translatedField d.coupledMean) s := by
        intro s
        exact pocketStopUnionLaw_stopHullInf_strip_marked hT' hTr hu₀ hh hC (by have := i.kappa_gt_four; linarith only [this]) hu₀' hX hζ
          hRc (hLc q) hR0 (hL0 q) hRm (hLm q) hdetR (hdetL q) hlocR (hlocL q)
          (wallsSigma_le hRm (hLm q)) (wallsSigma_le_drivingFiltration hX d.rightWall (d.leftWall q)) hRm' hLm'
          hG0 hcfgInf hA hAG (fun ω hω => hζG ω (hAG hω).1) hJordan hPoint s (hSidePrefix j hj s)
      exact current_sideLimits_of_raw_references (j.target i d) (side j) (j.hull d)
        (hSidePrefix j hj) hA (hSideDomainIn j hj)
        hDriven (hSideChart j hj) (hSideDomainMeasurable j hj)
        (hSideOpen j hj) (hSideActive j hj) (hSideHullOpen j hj)
        (isZeroBoundaryGFF_centredField hC hu₀') (hSideExterior j hj) hUnion
        (hSideInfo j hj) (hSideReferenceUnion j hj) (hSideReferenceMarks j hj)
        (hSideReferenceMeasurable j hj) (hSideReferenceLocal j hj) (hSideReferenceUnbounded j hj)
        (hSideReferenceMean j hj) (hSideJordan j hj) (hSideClosure j hj)
        (hSideRealCorner j hj) (hSideWallFaces j hj) (hSideOldHullSeparation j hj)
        (hSideOwnHeights j hj) (hSideInheritedArguments j hj) (hSidePhaseMeasurable j hj)
        (hSidePhaseZero j hj)

end InteractingSLE.Wire
