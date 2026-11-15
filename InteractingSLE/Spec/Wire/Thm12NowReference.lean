/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NowPocket
import InteractingSLE.Spec.Sec7.RefWireSide
import InteractingSLE.Spec.Sec7.RefWireOuter

/-! # Per-seed determination and R.7 after the reference and outer-arm reductions -/

set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets WangWu WholeField Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.RefWire

namespace Now

/-- The extremal parameter range of Aux. 131. -/
structure Extremal where
  kappa : ℝ
  leftWeight : ℝ
  rightWeight : ℝ
  kappa_gt_four : 4 < kappa
  left_gt : -2 < leftWeight
  right_gt : -2 < rightWeight
  max_eq : max leftWeight rightWeight = kappa / 2 - 4

/-- Reference data only. The per-seed record and marked laws are constructed by RefWire. -/
structure ReferenceObjects (Ω : Type u) [mΩ : MeasurableSpace Ω] where
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

end Now

/-- The unchanged source conclusion with all remaining RefWire premises named. -/
theorem now_pocketChartFieldStatement {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (d : Now.ReferenceObjects Ω) [IsProbabilityMeasure d.measure]
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
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)] G → 0 < d.measure G →
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
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)} (centredField d.translatedField d.coupledMean) d.harmonic)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField d.translatedField d.coupledMean ω + smoothDist upperHalfPlaneOpens d.harmonic) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂d.measure, Γ' ω = fun t : ℝ≥0 => d.curve ω t)
    : Lemma725RefSafe.PocketChartFieldStatement.{u} i.kappa i.leftWeight i.rightWeight := by
  exact RefWire.pocketChartFieldStatement_of_sideLimit_perQ i.kappa_gt_four i.left_gt i.left_lt i.right_gt i.right_lt
    hT' hTr hu₀ hh hC
    hu₀' hX hζ hRm hLm
    hRc hLc hR0 hL0 hβm
    hηm hηc hηH hη0 hR
    hβ hLw hnohit hlate htrace
    hav hattach hattachI hdetR hdetL
    hlocR hlocL hu hub hside
    h513

/-- The unchanged source conclusion with all remaining RefWire premises named. -/
theorem now_r7PocketStopStatement {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : Now.Extremal) (d : Now.ReferenceObjects Ω) [IsProbabilityMeasure d.measure]
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω) (d.chartField ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean)
    (hX : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hζ : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous ((d.leftWall 1) ω))
    (hR0 : ∀ ω, d.rightWall ω 0 = 0)
    (hL0 : ∀ ω, (d.leftWall 1) ω 0 = 0)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ t, Measurable fun ω => (d.leftWall 1) ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (d.leftWall 1) ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
    (hlocR : Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
    (hlocL : Sec6.IsEntranceHistoryLocal (d.leftWall 1) (centredField d.field d.originalMean) d.measure)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
    (hηc : ∀ ω, ContinuousOn (d.curve ω) (Ici 0))
    (hη0 : ∀ ω, d.curve ω 0 = 0)
    (hR : ∀ᵐ ω ∂d.measure, IsSimpleProper (d.rightWall ω) ∧ IsWallReverseVisit (d.rightWall ω) (d.curve ω) ∧ IsWallVisited (d.rightWall ω) (d.curve ω))
    (hL : ∀ᵐ ω ∂d.measure, IsSimpleProper ((d.leftWall 1) ω) ∧ IsWallReverseVisit ((d.leftWall 1) ω) (d.curve ω))
    (hne : ∀ᵐ ω ∂d.measure, range ((d.leftWall 1) ω) ≠ range (d.rightWall ω))
    (hord : ∀ᵐ ω ∂d.measure, Disjoint (range (d.rightWall ω)) (leftSideOf (range ((d.leftWall 1) ω))))
    (htrace : ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) ∧
      Continuous (fun s : ℝ => d.driver s.toNNReal ω) ∧ d.driver 0 ω = 0)
    (hattach : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (d.curve ω) (cfPocket (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
        (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) (cfArcL (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 1))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 0)))
    (hattachI : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖d.curve ω t‖) atTop atTop ∧ IsWallVisited ((d.leftWall 1) ω) (d.curve ω) ∧
        Sec6.AttachmentConstancyInf (d.curve ω) (cfPocket (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
          (cfArcRInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) (cfArcLInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
          (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 0)))
    (hu : InnerProductSpace.HarmonicOnNhd d.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall 1)] G → 0 < d.measure G →
      (∀ ω ∈ G, IsChangeConfigInc (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) →
      (∀ ω ∈ G, d.lifetime ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
        IsCfPocketConfig (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) →
      (∀ ω ∈ G, rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω)) →
      TwoSeedSideInput i.kappa i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall 1)) d.measure d.rightWall (d.leftWall 1) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)} (centredField d.translatedField d.coupledMean) d.harmonic ∧
        TwoSeedSideInputInf i.kappa i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall 1)) d.measure d.rightWall (d.leftWall 1) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)} (centredField d.translatedField d.coupledMean) d.harmonic)
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField d.translatedField d.coupledMean ω + smoothDist upperHalfPlaneOpens d.harmonic) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂d.measure, Γ' ω = fun t : ℝ≥0 => d.curve ω t)
    : R7Pocket.R7PocketStopStatement.{u} i.kappa i.leftWeight i.rightWeight R7Aux131.GoodR7 := by
  exact RefWire.r7PocketStopStatement_of_sideLimit (by have := i.kappa_gt_four; linarith only [this])
    hT' hTr hu₀ hh hC
    hu₀' hX hζ hRc hLc
    hR0 hL0 hRm hLm hdetR
    hdetL hlocR hlocL hηm hηc
    hη0 hR hL hne hord
    htrace hattach hattachI hu hub
    hside h513

end InteractingSLE.Wire
