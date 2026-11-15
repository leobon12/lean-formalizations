/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideIn
import InteractingSLE.Spec.Sec7.PocketSideInRefLaws
import InteractingSLE.Spec.Sec7.PocketSideInRefPhase

/-! # Native per-q side inputs after the landed geometry discharges -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets WangWu WholeField Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt

/-- The sixteen remaining reference inputs give the native per-q side input.
The canonical chart, actual corner and eight geometry/context facts are proved. -/
theorem now_pocketSideInput {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
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
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall q ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean)
      d.measure)
    (hlocL : ∀ q, Sec6.IsEntranceHistoryLocal (d.leftWall q) (centredField d.field d.originalMean)
      d.measure)
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
    : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)] G → 0 < d.measure G →
      (∀ ω ∈ G, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, d.lifetime ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
        IsCfPocketConfig (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) →
      (∀ ω ∈ G, rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) →
      PocketSideLimitInput0 (16 / i.kappa) i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall q)) d.measure d.rightWall (d.leftWall q) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)} (centredField d.translatedField d.coupledMean) d.harmonic ∧
        PocketSideLimitInputInf0 (16 / i.kappa) i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall q)) d.measure d.rightWall (d.leftWall q) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)} (centredField d.translatedField d.coupledMean) d.harmonic := by
  have hSideDomainIn := fun (j : SideTest Ω) (hj : j.Ready d) => SideTest.measurableSet_domainIn (i := i) hj hRc (hLc j.seed)
  have hSideChart := fun (j : SideTest Ω) (hj : j.Ready d) => SideTest.isPocketChartOn (i := i) hj hRc (hLc j.seed)
  have hSideDomainMeasurable := fun (j : SideTest Ω) (hj : j.Ready d) => SideTest.measurableSet_domain (i := i) hj hRc (hLc j.seed)
  have hSideOpen := fun (j : SideTest Ω) (hj : j.Ready d) => SideTest.isOpen_domain (i := i) hj
  have hSideActive := fun (j : SideTest Ω) (hj : j.Ready d) => SideTest.activeDom_eq (i := i) hj hRc (hLc j.seed)
  have hSideHullOpen := fun (j : SideTest Ω) (hj : j.Ready d) => fun (q : ℝ≥0) (ω : Ω) (hω : ω ∈ (j.target i d).event) (_ : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) => SideTest.isOpen_hull_compl (i := i) hj q ω hω
  have hSideJordan := fun (j : SideTest Ω) (hj : j.Ready d) => SideTest.jordan_cases (i := i) hj
  have hSideClosure := fun (j : SideTest Ω) (hj : j.Ready d) => SideTest.closure_domain (i := i) hj
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
      exact current_sideLimits_of_raw_references (j.target i d) {side j with seed := j.incomingSeed d} (j.hull d)
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
      exact current_sideLimits_of_raw_references (j.target i d) {side j with seed := j.incomingSeed d} (j.hull d)
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
      exact current_sideLimits_of_raw_references (j.target i d) {side j with seed := j.incomingSeed d} (j.hull d)
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
      exact current_sideLimits_of_raw_references (j.target i d) {side j with seed := j.incomingSeed d} (j.hull d)
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
