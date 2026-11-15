/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12BeaconFibre
import InteractingSLE.Spec.Wire.Thm12RelayChart
import InteractingSLE.Spec.Wire.Thm12BeaconInputs

/-! # Theorems 1.2 and 1.3 from the corrected, explicit-data frontier

R83 cap-continuous A.1 cores, physical marked fibre geometry and R.5 up to
phase are explicit. Two-mark exclusion and outer-pocket geometry are proved.
-/

set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire

open Wire Current Sec7 LocalSets WangWu WholeField StripWall Sec7.PocketStopField Sec7.PocketStopWalls
  Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.RefWire Sec7.PocketWordIn StripSysField
open Sec5.Prop59Pieces Sec5.Prop59NodeTree Sec5.CrossCond.StagedK2 Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedCand
  Sec5.Prop513Bridge
open Sec7.Aux119Heights Sec7.PhaseSel
open Exist.Staged (IsRegularDriver)
open Sec4 Sec5 Sec5.Prop513Schedule Sec5.Prop513Target Sec5.Prop513TreeExtract Sec5.Prop513Asm
  Sec5.Prop59Sched Sec5.Prop59Stage Sec5.Prop59System Sec5.StripRevVisit Sec5.Prop59Nodes
open Restart Exist Exist.Staged Exist.StagedLaw


open Sec7.StripMarks


variable
    (hG3C : ∀ κ, ZhanGT4.A1RLaw.G3RectLawC κ)
    (hEightC : ∀ κ, ZhanGT4.A1RLaw.EightRectLawC κ)
    (restartData : Relay.RestartDataOn.{u})
    (hRestartFacts : Relay.RestartFactsOn restartData)
    (markedData : Beacon.MarkedDataOn restartData)
    (hMarkedContext : Beacon.MarkedContextOn restartData markedData)
    (hMarkedZero : Beacon.MarkedZeroFieldOn restartData markedData)
    (hMarkedLocal : Beacon.MarkedLocalOn restartData markedData)
    (hMarkedGeometry : Beacon.MarkedGeometryOn restartData markedData)
    (hMeanHarmonic : Beacon.MeanHarmonicOn restartData)
    (hSlitBoundary : Beacon.SlitBoundaryOn restartData markedData)
    (restartData0 : Relay.RestartDataOn.{0})
    (hRestartFacts0 : Relay.RestartFactsOn restartData0)
    (markedData0 : Beacon.MarkedDataOn restartData0)
    (hMarkedContext0 : Beacon.MarkedContextOn restartData0 markedData0)
    (hMarkedZero0 : Beacon.MarkedZeroFieldOn restartData0 markedData0)
    (hMarkedLocal0 : Beacon.MarkedLocalOn restartData0 markedData0)
    (hMarkedGeometry0 : Beacon.MarkedGeometryOn restartData0 markedData0)
    (hMeanHarmonic0 : Beacon.MeanHarmonicOn restartData0)
    (hSlitBoundary0 : Beacon.SlitBoundaryOn restartData0 markedData0)
    (hChartRaw : Relay.RawChartMembersOn.{0})
    (stageObjects : Night.StageObjectsOn)
    (hRootLater : Night.RootLaterOn (Beacon.cond44 hG3C hEightC)
      (Beacon.stages (Beacon.cond44 hG3C hEightC) stageObjects))
    (hNodeLaw : Night.NodeLawOn (Beacon.cond44 hG3C hEightC)
      (Beacon.stages (Beacon.cond44 hG3C hEightC) stageObjects))
    (hWordPhase : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseCont.R7PhaseWordRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuterCont : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{0} k rL rR)
    (hShared : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → OuterPhNext.R7OuterSharedVisitsRemaining.{0} k rL rR)

variable (Ωw : BothLow → Type) [mWord : ∀ i, MeasurableSpace (Ωw i)]
    [hWordBorel : ∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [hWordProbability : ∀ i, IsProbabilityMeasure (baseWord i).measure]
    (wordSide : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i))
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hWordGFF : ∀ i, IsGFFWithBoundaryData (baseWord i).measure (baseWord i).field
      (baseWord i).boundary (baseWord i).jumps)
    (hWordCF : ∀ i, IsCenteredCounterflowDriver (16 / i.kappa) (baseWord i).measure (baseWord i).field
      (baseWord i).driver (baseWord i).lifetime)
    (hWordLife : ∀ i, ∀ᵐ ω ∂(baseWord i).measure, (baseWord i).lifetime ω = ⊤)

variable (hWordleft : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ a ∈
  Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
variable (hWordright : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ a ∈
  Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
variable (hWordθ₁ : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; x.thetaR
  ∈ Ioo (-(π / 2)) (π / 2))
variable (hWordθ₂ : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; x.thetaL
  ∈ Ioc (-(π / 2)) (π / 2))
variable (hWordu₀ : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i;
  IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
variable (hWordvα : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i;
  IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1
      x.rightWall)
variable (hWordvL : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ q,
  IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt
      (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
variable (hWordβc : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ ω,
  Continuous (x.outerWall ω))
variable (hWordβ0 : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ ω,
  x.outerWall ω 0 = 0)
variable (hWordβm : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ t,
  Measurable fun ω => x.outerWall ω t)
variable (hWordβtr : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ᵐ ω
  ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec
      0 ω).1 ⊤ (x.outerWall ω))
variable (hWordηc : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ ω,
  ContinuousOn (x.curve ω) (Ici 0))
variable (hWordηH : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ ω, ∀ t
  : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
variable (hWordη0 : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ ω,
  x.curve ω 0 = 0)
variable (hWordηm : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ t : ℝ,
  0 ≤ t → Measurable fun ω => x.curve ω t)
variable (hWordηtr : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ᵐ ω
  ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0
      => x.curve ω t))
variable (hWordu : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i;
  InnerProductSpace.HarmonicOnNhd x.harmonic H)
variable (hWordub : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∃ M : ℝ,
  ∀ z ∈ H, |x.harmonic z| ≤ M)
variable (hWord𝔥 : ∀ i, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) i; ∀ φ :
  TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
variable (hSidepre : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord
      hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤
        (mWord index))
variable (hSideFo : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord
      hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
variable (hSideRawReference : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event
        target.curve target.domain (refs.sets i) target.zeroField refs.level)
variable (hSideLattice : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife
        (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
variable (hSideCollar : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀
        gB : ℕ → (Ωw index) → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level)
          target.zeroField target.measure (gB i)) →
      ∀ g : (Ωw index) → DistOn upperHalfPlaneOpens, IsLocalSetMean ((activeCompl target.event target.curve
          target.baseChart) q) target.zeroField target.measure g →
      ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve target.baseChart)
            q ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (activeCompl target.event target.curve
              target.baseChart) q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve
                ω) q)
            (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve
                ω) q) →
            ∃ (i : ℕ) (b d : ℝ),
              let inv := (relChart target.baseChart target.curve q ω).2.1;
              let vB := harmRep (gB i ω) (H \ liveExt target.event target.curve target.domain (refs.sets i)
                  refs.level ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + target.harmonic (inv y) + chiC target.kappa * refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) - refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
                (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver
                    (target.curve ω) q)
                (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver
                    (target.curve ω) q)
                ξ + refs.phase q ω * (Ioo
                  (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                    zL q ω - segDriver (target.curve ω) q)
                  (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                    zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - refs.offset)
variable (hSideProbes : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
variable (hSideJointGerms : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, ∀ᵐ ω ∂target.measure, ω ∈ target.event → ω ∈ refs.event i →
      ∃ (ξ η y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU b : ℝ),
        IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
        (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
        ContinuousOn (fun y : ℝ => L y) J ∧
        (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
        bC = bU ∧ bU = bC + chiC target.kappa * (L y₀).im ∧
        ContinuousWithinAt L Hbar (ξ : ℂ) ∧
        Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) ∧
        Tendsto (refs.currentMean i ω) (𝓝[H] (ξ : ℂ)) (𝓝 (b + refs.phase (refs.visit i ω) ω)) ∧
        Tendsto (refs.referenceMean i ω) (𝓝[H] (η : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => refs.referenceMean i ω (φ z) - refs.currentMean i ω z - chiC target.kappa * (L z).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 0))
variable (hSideVisits : ∀ index,
    let i := index
    let x := (Relay.words (Beacon.cond44 hG3C hEightC)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)

variable (hRefWord : ∀ index, let x := (Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb) index;
  ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)

namespace Beacon

section
include hG3C hEightC hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0
  hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr hWordu hWordub
  hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits hRefWord

/-- The pointwise WORDSAFE assembly using corrected A.1 cores. -/
theorem determinationReferenceFamily
    (hChart0 : Sec5.CfGiven.CfGivenChartStatement.{0})
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hLaws : Hsd.Fig51CandLawsStatement (Beacon.cond44 hG3C hEightC)) : Aux50Hit.Lemma725DetReferenceStatement.{u} := by
  let word := Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb
  have hWordT := Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb
    hWordGFF hWordCF hWordLife hWordleft hWordright
  apply lemma725DetReferenceStatement_ulift.{0, u}
  apply Lemma725RefSafe.lemma725DetReferenceStatement_of_pocketChartField
  intro κ hκ rL rR hL hLd hR hRd
  let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
  have hA2 := late_fourForceCrosscutG3LifeStatement (fun κ => Beacon.coreG3_of_lawC (hG3C κ))
  have hA2' := late_threeForceCrosscutEightStatement (fun κ => Beacon.coreEight_of_lawC (hEightC κ))
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have haux : Sec4.Aux7Statement.{0} i.kappa := by
    have hs : Sec4.Aux7Statement.{0} (16 / (16 / i.kappa)) :=
      Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA (hWordT i).kappa_pos (hWordT i).kappa_lt_four
    have heq : 16 / (16 / i.kappa) = i.kappa := by field_simp
    rw [← heq]
    exact @hs
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨-, -, hC, hu'⟩ := counterflowObjects_spec (hWordT i).counterflow
  let _ : IsProbabilityMeasure (wordSafeObjects i (word i) (hWordT i)).measure := by
    change IsProbabilityMeasure (word i).measure
    infer_instance
  have hside := late_pocketSideInput i (wordSafeObjects i (word i) (hWordT i)) (wordSide i)
    (by simpa only [wordSafeObjects, hdual] using hC)
    (by simpa only [wordSafeObjects, hdual] using hu')
    (hWordvα i).continuous (fun q => (hWordvL i q).continuous)
    (hSidepre i) (hSideFo i) (hSideRawReference i) (hSideLattice i)
    (hSideCollar i) (hSideProbes i) (hSideJointGerms i) (hSideVisits i)
  exact wordSafe_pocketChartField i (word i) (fun κ => Beacon.coreG3_of_lawC (hG3C κ))
    (fun κ => Beacon.coreEight_of_lawC (hEightC κ))
    hQ0 haux h411
    (wordSafe_switched hA hChart0) (hWordT i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i)
    (hWordu₀ i) (hWordvα i) (hWordvL i) (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i)
    (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i) (hWordηtr i) (hWordu i) (hWordub i) hside
    (aux130RefFrame i) (aux130RefFrame_bounds i) (hRefWord i) hLaws

end

section
include hG3C hEightC hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0
  hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr hWordu hWordub
  hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits hWord𝔥

/-- The pointwise WORDSAFE assembly using corrected A.1 cores. -/
theorem pocketWordFamily
    (hChart0 : Sec5.CfGiven.CfGivenChartStatement.{0}) : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 →
    -2 < rR → rR < κ / 2 - 4 → Lemma725Ref.PocketWordEvolution.{0} κ rL rR := by
  let word := Relay.words (Beacon.cond44 hG3C hEightC) baseWord hWordb
  have hWordT := Relay.wordT (Beacon.cond44 hG3C hEightC) baseWord hWordb
    hWordGFF hWordCF hWordLife hWordleft hWordright
  have hA2 := late_fourForceCrosscutG3LifeStatement (fun κ => Beacon.coreG3_of_lawC (hG3C κ))
  have hA2' := late_threeForceCrosscutEightStatement (fun κ => Beacon.coreEight_of_lawC (hEightC κ))
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h44 := Sec5.Prop513Asm.theorem12ParamCond44Statement_of_lemma47Q_of_A2 h470 hA2 hA2'
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have hSwitched := wordSafe_switched hA hChart0
  intro κ hκ rL rR hL hLd hR hRd
  let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
  have haux : Sec4.Aux7Statement.{0} i.kappa := by
    have hs : Sec4.Aux7Statement.{0} (16 / (16 / i.kappa)) :=
      Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA (hWordT i).kappa_pos (hWordT i).kappa_lt_four
    have heq : 16 / (16 / i.kappa) = i.kappa := by field_simp
    rw [← heq]
    exact @hs
  exact wordSafe_pocketWordEvolution i (word i) h44 haux h411 h470 hSwitched
    (hWordT i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i)
    (hWordu₀ i) (hWordvα i) (hWordvL i) (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i) (hWordηc i)
    (hWordηH i) (hWordη0 i) (hWordηm i) (hWordηtr i) (hWordu i) (hWordub i) (hWord𝔥 i) (wordSide i)
    (hSidepre i) (hSideFo i) (hSideRawReference i) (hSideLattice i) (hSideCollar i) (hSideProbes i)
    (hSideJointGerms i) (hSideVisits i)
end

end Beacon


section
include hG3C hEightC restartData0 hRestartFacts0 markedData0 hMarkedContext0 hMarkedZero0 hMarkedLocal0 hMarkedGeometry0
  hMeanHarmonic0 hSlitBoundary0 hChartRaw stageObjects hRootLater hNodeLaw hWordPhase hOuterCont hShared hWordBorel
  hWordProbability hWordb hWordGFF hWordCF hWordLife hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL
  hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 hSidepre hSideFo
  hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits restartData hRestartFacts
  markedData hMarkedContext hMarkedZero hMarkedLocal hMarkedGeometry hMeanHarmonic hSlitBoundary hRefWord

/-- Theorem 1.2 from the current explicit-data mathematical leaves. -/
theorem theorem12Statement_beacon_expanded : Exist.Theorem12Statement.{u} := by
  have hG := fun κ => Beacon.coreG3_of_lawC (hG3C κ)
  have hE := fun κ => Beacon.coreEight_of_lawC (hEightC κ)
  have hA := late_partAInputs hG hE
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := Beacon.cond44 hG3C hEightC
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h4110 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  obtain ⟨hQ0, hChart0⟩ := Relay.qAndChart_of_raw h44 h470 hA
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h4110) hChartRaw
  have hDy0 := Beacon.dyCover_of_marked restartData0 hRestartFacts0 markedData0 hMarkedContext0
    hMarkedZero0 hMarkedLocal0 hMarkedGeometry0 hMeanHarmonic0 hSlitBoundary0
  have hLaws : Hsd.Fig51CandLawsStatement h44 :=
    Night.fig51CandLaws_of_parts h44 hA (Beacon.stages h44 stageObjects)
      (Beacon.rootPath h44 hA stageObjects) hRootLater hNodeLaw (Beacon.nodeBase h44 stageObjects)
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws hWordPhase hOuterCont hShared
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  have hA2 := late_fourForceCrosscutG3LifeStatement hG
  have hA20 := late_threeForceCrosscutEightStatement hE
  have hDy := Beacon.dyCover_of_marked restartData hRestartFacts markedData hMarkedContext
    hMarkedZero hMarkedLocal hMarkedGeometry hMeanHarmonic hSlitBoundary
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have h51 := Beacon.prop51 hA hDy
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  apply theorem12Statement_current hA2 hA20 h47
    (Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg h51) hR7
  · apply Beacon.pocketWordFamily (Ωw := Ωw) (baseWord := baseWord) (wordSide := wordSide) <;> assumption
  · apply Beacon.determinationReferenceFamily (Ωw := Ωw) (baseWord := baseWord) (wordSide := wordSide) <;> assumption
end

section
include hG3C hEightC restartData0 hRestartFacts0 markedData0 hMarkedContext0 hMarkedZero0 hMarkedLocal0 hMarkedGeometry0
  hMeanHarmonic0 hSlitBoundary0 hChartRaw stageObjects hRootLater hNodeLaw hWordPhase hOuterCont hShared hWordBorel
  hWordProbability hWordb hWordGFF hWordCF hWordLife hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL
  hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 hSidepre hSideFo
  hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits

/-- Theorem 1.3 from the current explicit-data mathematical leaves. -/
theorem theorem13Statement_beacon_expanded : Exist.Theorem13Statement.{u} := by
  have hG := fun κ => Beacon.coreG3_of_lawC (hG3C κ)
  have hE := fun κ => Beacon.coreEight_of_lawC (hEightC κ)
  have hA := late_partAInputs hG hE
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := Beacon.cond44 hG3C hEightC
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h4110 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  obtain ⟨hQ0, hChart0⟩ := Relay.qAndChart_of_raw h44 h470 hA
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h4110) hChartRaw
  have hDy0 := Beacon.dyCover_of_marked restartData0 hRestartFacts0 markedData0 hMarkedContext0
    hMarkedZero0 hMarkedLocal0 hMarkedGeometry0 hMeanHarmonic0 hSlitBoundary0
  have hLaws : Hsd.Fig51CandLawsStatement h44 :=
    Night.fig51CandLaws_of_parts h44 hA (Beacon.stages h44 stageObjects)
      (Beacon.rootPath h44 hA stageObjects) hRootLater hNodeLaw (Beacon.nodeBase h44 stageObjects)
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws hWordPhase hOuterCont hShared
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  have hA2 := late_fourForceCrosscutG3LifeStatement hG
  have hA20 := late_threeForceCrosscutEightStatement hE
  have h51 := Beacon.prop51 hA hDy0
  apply theorem13Statement_current h470 h51 hR7
  · apply Beacon.pocketWordFamily (Ωw := Ωw) (baseWord := baseWord) (wordSide := wordSide) <;> assumption
  · exact hA2
  · exact hA20
end

end InteractingSLE.Wire
