/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NowSide
import InteractingSLE.Spec.Sec7.PocketWordInVisitStrip

/-! # The pocket word with the actual strip objects and remaining side references -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire

open Current Sec7 LocalSets WangWu WholeField StripWall StripSideHeightProb StripPocketPath
  Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I
  Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks Sec7.PocketWordAssembly Sec7.PocketSeedOpen
  Sec7.PocketUnionPt Sec7.PocketStop Sec7.PocketStopWallsFin Sec7.PocketStopMarked
  Sec7.PocketLeftFrontier Sec7.StripPocketConfig Sec7.PocketWordPerQ Sec7.PocketStopSide
  Sec7.PocketTraversal Sec7.PocketAdapt Sec7.PocketWordIn
open Exist.Staged (IsRegularDriver)

namespace Now

/-- Source experiment data. No law or geometric conclusion is stored here. -/
structure StripObjects (Ω : Type) [mΩ : MeasurableSpace Ω] where
  measure : Measure Ω
  boundary : ℝ → ℝ
  jumps : Finset ℝ
  field : Ω → DistOn upperHalfPlaneOpens
  driver : ℝ≥0 → Ω → ℝ
  lifetime : Ω → ℝ≥0∞
  experiment : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞
  thetaR : ℝ
  thetaL : ℝ
  originalMean : ℂ → ℝ
  rightWall : Ω → ℝ≥0 → ℂ
  outerWall : Ω → ℝ≥0 → ℂ
  leftWall : ℚ → Ω → ℝ≥0 → ℂ
  curve : Ω → ℝ → ℂ
  harmonic : ℂ → ℝ
  mean : DistOn upperHalfPlaneOpens

/-- The actual counterflow witness determines the old data-only side-test frame. -/
def wordObjects {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment) : WordObjects Ω :=
  let c := counterflowObjects hS.counterflow
  { measure := x.measure
    nL := flowLineNL c.boundary c.jumps 0
    nR := flowLineNR c.boundary c.jumps 0
    xL := flowLineXL c.boundary c.jumps 0
    xR := flowLineXR c.boundary c.jumps 0
    rhoL := flowLineRhoL (16 / (16 / i.kappa)) c.boundary c.jumps 0 0
    rhoR := flowLineRhoR (16 / (16 / i.kappa)) c.boundary c.jumps 0 0
    field := x.field
    chartField := c.sourceField
    translatedField := c.field
    scale := -(Real.pi * chiC (16 / i.kappa))
    chartConstant := chiC (16 / (16 / i.kappa))
    translateConstant := 0 * chiC (16 / (16 / i.kappa))
    originalMean := x.originalMean
    filtration := c.filtration
    driver := x.driver
    forceL := c.left
    forceR := c.right
    brownian := c.brownian
    lifetime := x.lifetime
    coupledMean := c.mean
    rightWall := x.rightWall
    outerWall := x.outerWall
    leftWall := x.leftWall
    curve := x.curve
    mean := x.mean
    harmonic := x.harmonic }

end Now

/-- Strip construction, Aux. 37 and the flat clock discharge the former wall,
field, avoidance and attachment premises. Only the three first-hit laws and
sixteen side-reference premises remain besides the source experiment facts. -/
theorem now_pocketWordEvolution {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (haux7 : Sec4.Aux7Statement.{0} i.kappa)
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (hS : StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field x.driver x.lifetime x.experiment)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθ₁ : x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
    (hr : ∀ j ω, IsRegularDriver (x.experiment (StripSys.alphaSpec x.thetaR) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (x.experiment (StripSys.betaSpec (StripSys.rt q) x.thetaL) j ω))
    (he : ∀ ω, IsRegularDriver (x.experiment StripSys.leftExtremalSpec 0 ω))
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hvα : IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1 x.rightWall)
    (hvL : ∀ q, IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
    (hβc : ∀ ω, Continuous (x.outerWall ω))
    (hβ0 : ∀ ω, x.outerWall ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => x.outerWall ω t)
    (hβtr : ∀ᵐ ω ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec 0 ω).1 ⊤ (x.outerWall ω))
    (hηc : ∀ ω, ContinuousOn (x.curve ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
    (hη0 : ∀ ω, x.curve ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => x.curve ω t)
    (hηtr : ∀ᵐ ω ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0 => x.curve ω t))
    (hfirstR : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂x.measure,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (x.rightWall ω)) (x.curve ω) q)
    (hfirstE : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂x.measure,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (x.outerWall ω)) (x.curve ω) q)
    (hfirstL : ∀ r : ℚ, 0 < r → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂x.measure,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (x.leftWall r ω)) (x.curve ω) q)
    (hu : InnerProductSpace.HarmonicOnNhd x.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
    (side : SideTest Ω → SideReferences Ω)
    (hSidePrefix : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d;
      ∀ q : ℝ≥0, locPrefixSigma target.walls target.event target.curve q ≤ mΩ)
    (hSideExterior : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      Measurable[germSigma (Sec7.Lemma725RefMarks.extA target.event target.domain)
        target.zeroField] refs.exterior)
    (hSideInfo : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let refs := side j;
      ∀ (q : ℝ≥0) i, refs.info q i ≤ mΩ)
    (hSideReferenceUnion : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i, PocketStopUnionLaw (target.walls ⊔ refs.info q i) target.measure target.event
        target.curve target.domain
      (fun ω => (j.hull d) q ω ∪ referenceHull refs.oldHull i ω) target.zeroField q)
    (hSideReferenceMarks : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i,
      MeasurableSpace.comap (activeCompl target.event target.curve target.baseChart q) hittingSigma
        ⊔
        MeasurableSpace.comap (referenceSet target.domain refs.oldHull i) hittingSigma ≤
      locPrefixSigma ((target.walls ⊔ MeasurableSpace.comap refs.exterior inferInstance) ⊔
        refs.info q i) target.event target.curve q)
    (hSideReferenceMeasurable : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, Measurable[mΩ, hittingSigma] (referenceSet target.domain refs.oldHull i))
    (hSideReferenceLocal : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, IsLocalSet (referenceSet target.domain refs.oldHull i) target.zeroField target.measure)
    (hSideReferenceUnbounded : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ i, ∀ᵐ ω ∂target.measure, ∀ z ∈ lowerUnion (referenceSet target.domain refs.oldHull i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (referenceSet target.domain refs.oldHull i ω))
        z))
    (hSideReferenceMean : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ (q : ℝ≥0) i, IsLocalSetMean (referenceSet target.domain refs.oldHull i) target.zeroField
        target.measure (refs.mean q i))
    (hSideRealCorner : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      j.incomingSeed d ω ∉ H → ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p : ℂ,
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ≠
          j.incomingSeed d ω)
    (hSideWallFaces : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p ∈ frontier (target.domain ω), p ∉ (j.hull d) q ω →
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ j : Fin 2, ξ ∈ refs.faces q (Sum.inl j) ω)
    (hSideOldHullSeparation : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ ξ : ℝ, ξ ∉ target.jumps q ω → ∀ p ∈ (j.hull d) q ω,
        Tendsto (relChart target.baseChart target.curve q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
          ∃ (s : ℚ≥0) (r : ℝ), 0 < r ∧ ξ ∈ refs.faces q (Sum.inr s) ω ∧
            refs.oldHull s ω ⊆ (j.hull d) q ω ∧ Disjoint (target.domain ω ∩ ((j.hull d) q ω \
              refs.oldHull s ω)) (ball p r))
    (hSideOwnHeights : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ReferenceHeightLimits (chiC target.kappa) target.measure target.event target.curve
        target.baseChart
      target.domain refs.oldHull q target.harmonic (refs.faces q) (refs.mean q) (refs.lift q)
        (refs.height q))
    (hSideInheritedArguments : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ReferenceLiftLimits target.measure target.event target.curve target.baseChart q
      (refs.faces q) (refs.lift q) (refs.branch q))
    (hSidePhaseMeasurable : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      Measurable[target.walls] refs.phase)
    (hSidePhaseZero : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d; let refs := side j;
      ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∀ i ξ, ξ ∈ refs.faces q i ω → refs.height q i ω ξ + chiC target.kappa *
        (2 * Real.pi * refs.branch q i ω ξ - 2 * Real.pi * refs.phase ω) =
      forceBoundaryData target.kappa target.rhoL target.rhoR
        (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver
          (target.curve ω) q)
        (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver
          (target.curve ω) q) ξ - refs.offset)
    : Lemma725Ref.PocketWordEvolution.{0} i.kappa i.leftWeight i.rightWeight := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by
    field_simp
  let d := Now.wordObjects i x hS
  letI : IsProbabilityMeasure d.measure := by
    change IsProbabilityMeasure x.measure
    infer_instance
  have hvLp : ∀ q : ℚ, 0 < q → IsWallVersion x.measure
      (x.experiment (StripSys.betaSpec (StripSys.rt q) x.thetaL)) (StripSys.rt q) (x.leftWall q) :=
    fun q hq => by simpa only [positiveSeed_of_pos hq] using hvL q
  have hw := fun q => wall_inputs h44 hS hleft hright (Ioo_subset_Icc_self hθ₁)
    (Ioc_subset_Icc_self hθ₂) (positiveSeed_pos q) hr (hl _ (positiveSeed_pos q)) hu₀ hvα (hvL q)
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hside := now_pocketSideInput i d side hT hTr hu₀.1
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀)
    (by simpa only [d, Now.wordObjects, hdual] using hC) (by simpa only [d, Now.wordObjects, hdual] using hu')
    (counterflowObjects_measurable hS.counterflow) hS.lifetime
    hvα.measurable (fun q => (hvL q).measurable) hvα.continuous (fun q => (hvL q).continuous)
    hvα.zero (fun q => (hvL q).zero) (hw 1).1 (fun q => (hw q).2.2.1)
    (hw 1).2.1 (fun q => (hw q).2.2.2)
    hSidePrefix hSideExterior hSideInfo hSideReferenceUnion
    hSideReferenceMarks hSideReferenceMeasurable hSideReferenceLocal hSideReferenceUnbounded
    hSideReferenceMean hSideRealCorner hSideWallFaces hSideOldHullSeparation
    hSideOwnHeights hSideInheritedArguments hSidePhaseMeasurable hSidePhaseZero
  have hp := pocketWordEvolution_of_stripSystem_firstHit h44
    (by rw [hdual]; exact haux7) h411 hS hleft hright hθ₁ hθ₂
    i.left_gt (by simpa only [hdual] using i.left_lt)
    i.right_gt (by simpa only [hdual] using i.right_lt)
    hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr hηc hηH hη0 hηm hηtr
    hfirstR hfirstE hfirstL x.mean hu hub h𝔥
    (by
      intro q hq G hG hPG hconf hζG hcfg hcfgI
      have hs := hside q hq G hG hPG hconf hζG hcfg hcfgI
      constructor
      · convert hs.1 using 1 <;> simp only [d, Now.wordObjects, hdual]
      · convert hs.2 using 1 <;> simp only [d, Now.wordObjects, hdual])
  simpa only [hdual] using hp

end InteractingSLE.Wire
