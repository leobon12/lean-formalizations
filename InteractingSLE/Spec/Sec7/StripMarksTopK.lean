/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12Late
import InteractingSLE.Spec.Sec7.StripMarksWireK

/-!
# Theorems 1.2 and 1.3 with Lemma 7.25's reference from the pocket word's strip objects (experiments constructed)

Packet PROVE-STRIPMARKS. The final form of the `hStripMarks` reduction:

* **`late_determinationReferenceFamily_stripK`**: `Aux50Hit.Lemma725DetReferenceStatement.{u}` from the pocket word's
  own strip family (`word`, `hWord*`, `wordSide`, `hSide*`, `hSwitched`) and, for each both-low pair, the Figure 5.1
  frame of its strip word (`refFrame`, `hRefBounds`, `hRefWord`) and the killed laws of the concrete root and node
  candidates of Proposition 5.13 (`hRefLaw₀`, `hRefLaw`, with their noise/past data `refNoise₀`, `refBase₀`,
  `hRefBase₀`, `refNoise`, `refBase`, `hRefBase` on an extension space `ΩRefStage`);
* **`theorem12Statement_stripMarksK`**: Theorem 1.2 (unchanged conclusion) = `Wire.theorem12Statement_late` with the
  reference block (59 binders) and `hQ` replaced by these 17 binders, and `hCrossLeft`/`hCrossRight` proved;
* **`theorem13Statement_stripMarksK`**: Theorem 1.3 (unchanged conclusion) = `Wire.theorem13Statement_late` with
  `hCrossLeft`/`hCrossRight` proved.

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.StripMarks

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

section Expanded
variable
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover : Sec5.Aux61R2.RefClockFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref)
    (hAvoid : ∀ κ b J I, Ref κ b J I → Sec5.Aux61Win.IsAvoidingRef.{u} κ b J I)
    (Ref0 : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover0 : Sec5.Aux61R2.RefClockFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref0)
    (hAvoid0 : ∀ κ b J I, Ref0 κ b J I → Sec5.Aux61Win.IsAvoidingRef.{0} κ b J I)
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hSwitched : Sec5.RestartGen.SwitchedWallFirstHitStatement.{0})
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR)

variable (Ωw : BothLow → Type) [mWord : ∀ i, MeasurableSpace (Ωw i)]
    [hWordBorel : ∀ i, StandardBorelSpace (Ωw i)]
    (word : ∀ i, Now.StripObjects (Ωw i)) [hWordProbability : ∀ i, IsProbabilityMeasure (word i).measure]
    (wordSide : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i))
variable (hWordS : ∀ i, let x := word i; StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field
      x.driver x.lifetime x.experiment)
variable (hWordleft : ∀ i, let x := word i; ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
variable (hWordright : ∀ i, let x := word i; ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
variable (hWordθ₁ : ∀ i, let x := word i; x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
variable (hWordθ₂ : ∀ i, let x := word i; x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
variable (hWordr : ∀ i, let x := word i; ∀ j ω, IsRegularDriver (x.experiment (StripSys.alphaSpec x.thetaR) j ω))
variable (hWordl : ∀ i, let x := word i; ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (x.experiment (StripSys.betaSpec (StripSys.rt q) x.thetaL) j ω))
variable (hWorde : ∀ i, let x := word i; ∀ ω, IsRegularDriver (x.experiment StripSys.leftExtremalSpec 0 ω))
variable (hWordu₀ : ∀ i, let x := word i; IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
variable (hWordvα : ∀ i, let x := word i; IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1
      x.rightWall)
variable (hWordvL : ∀ i, let x := word i; ∀ q, IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt
      (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
variable (hWordβc : ∀ i, let x := word i; ∀ ω, Continuous (x.outerWall ω))
variable (hWordβ0 : ∀ i, let x := word i; ∀ ω, x.outerWall ω 0 = 0)
variable (hWordβm : ∀ i, let x := word i; ∀ t, Measurable fun ω => x.outerWall ω t)
variable (hWordβtr : ∀ i, let x := word i; ∀ᵐ ω ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec
      0 ω).1 ⊤ (x.outerWall ω))
variable (hWordηc : ∀ i, let x := word i; ∀ ω, ContinuousOn (x.curve ω) (Ici 0))
variable (hWordηH : ∀ i, let x := word i; ∀ ω, ∀ t : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
variable (hWordη0 : ∀ i, let x := word i; ∀ ω, x.curve ω 0 = 0)
variable (hWordηm : ∀ i, let x := word i; ∀ t : ℝ, 0 ≤ t → Measurable fun ω => x.curve ω t)
variable (hWordηtr : ∀ i, let x := word i; ∀ᵐ ω ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0
      => x.curve ω t))
variable (hWordu : ∀ i, let x := word i; InnerProductSpace.HarmonicOnNhd x.harmonic H)
variable (hWordub : ∀ i, let x := word i; ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
variable (hWord𝔥 : ∀ i, let x := word i; ∀ φ : TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
variable (hSidepre : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤
        (mWord index))
variable (hSideFo : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
variable (hSideRawReference : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event
        target.curve target.domain (refs.sets i) target.zeroField refs.level)
variable (hSideLattice : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife
        (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
variable (hSideCollar : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
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
variable (hSideProbes : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
variable (hSideJointGerms : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
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
variable (hSideVisits : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)

variable (Ωa : Now.Extremal → Type) [mAux : ∀ i, MeasurableSpace (Ωa i)]
    [hAuxBorel : ∀ i, StandardBorelSpace (Ωa i)]
    (aux131 : ∀ i, Now.ReferenceObjects (Ωa i)) [hAuxProbability : ∀ i, IsProbabilityMeasure (aux131 i).measure]
variable (hAuxT' : ∀ index, let d := aux131 index; ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale
      d.chartConstant (d.field ω) (d.chartField ω))
variable (hAuxTr : ∀ index, let d := aux131 index; ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω)
      (d.translatedField ω))
variable (hAuxu₀ : ∀ index, let d := aux131 index; InnerProductSpace.HarmonicOnNhd d.originalMean H)
variable (hAuxh : ∀ index, let d := aux131 index; IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field
      d.originalMean) d.measure)
variable (hAuxC : ∀ index, let i := index; let d := aux131 index; IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL
      d.rhoR d.measure d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
variable (hAuxu₀' : ∀ index, let i := index; let d := aux131 index; IsBoundedHarmonicExtension (forceBoundaryData
      i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean)
variable (hAuxX : ∀ index, let d := aux131 index; IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
variable (hAuxζ : ∀ index, let d := aux131 index; ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
variable (hAuxRc : ∀ index, let d := aux131 index; ∀ ω, Continuous (d.rightWall ω))
variable (hAuxLc : ∀ index, let d := aux131 index; ∀ ω, Continuous ((d.leftWall 1) ω))
variable (hAuxR0 : ∀ index, let d := aux131 index; ∀ ω, d.rightWall ω 0 = 0)
variable (hAuxL0 : ∀ index, let d := aux131 index; ∀ ω, (d.leftWall 1) ω 0 = 0)
variable (hAuxRm : ∀ index, let d := aux131 index; ∀ t, Measurable fun ω => d.rightWall ω t)
variable (hAuxLm : ∀ index, let d := aux131 index; ∀ t, Measurable fun ω => (d.leftWall 1) ω t)
variable (hAuxdetR : ∀ index, let d := aux131 index; ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
variable (hAuxdetL : ∀ index, let d := aux131 index; ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (d.leftWall 1) ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
variable (hAuxlocR : ∀ index, let d := aux131 index; Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field
      d.originalMean) d.measure)
variable (hAuxlocL : ∀ index, let d := aux131 index; Sec6.IsEntranceHistoryLocal (d.leftWall 1) (centredField d.field
      d.originalMean) d.measure)
variable (hAuxηm : ∀ index, let d := aux131 index; ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
variable (hAuxηc : ∀ index, let d := aux131 index; ∀ ω, ContinuousOn (d.curve ω) (Ici 0))
variable (hAuxη0 : ∀ index, let d := aux131 index; ∀ ω, d.curve ω 0 = 0)
variable (hAuxR : ∀ index, let d := aux131 index; ∀ᵐ ω ∂d.measure, IsSimpleProper (d.rightWall ω) ∧
      IsWallReverseVisit (d.rightWall ω) (d.curve ω) ∧ IsWallVisited (d.rightWall ω) (d.curve ω))
variable (hAuxL : ∀ index, let d := aux131 index; ∀ᵐ ω ∂d.measure, IsSimpleProper ((d.leftWall 1) ω) ∧
      IsWallReverseVisit ((d.leftWall 1) ω) (d.curve ω))
variable (hAuxne : ∀ index, let d := aux131 index; ∀ᵐ ω ∂d.measure, range ((d.leftWall 1) ω) ≠ range (d.rightWall ω))
variable (hAuxord : ∀ index, let d := aux131 index; ∀ᵐ ω ∂d.measure, Disjoint (range (d.rightWall ω)) (leftSideOf
      (range ((d.leftWall 1) ω))))
variable (hAuxtrace : ∀ index, let d := aux131 index; ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver
      s.toNNReal ω) (d.curve ω) ∧
      Continuous (fun s : ℝ => d.driver s.toNNReal ω) ∧ d.driver 0 ω = 0)
variable (hAuxattach : ∀ index, let d := aux131 index; ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc
      (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (d.curve ω) (cfPocket (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
        (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) (cfArcL (d.rightWall ω) ((d.leftWall 1) ω)
            (StripSys.rt q))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 1))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 0)))
variable (hAuxattachI : ∀ index, let d := aux131 index; ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc
      (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖d.curve ω t‖) atTop atTop ∧ IsWallVisited ((d.leftWall 1) ω) (d.curve ω) ∧
        Sec6.AttachmentConstancyInf (d.curve ω) (cfPocket (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
          (cfArcRInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) (cfArcLInf (d.rightWall ω) ((d.leftWall 1)
              ω) (StripSys.rt q))
          (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 0)))
variable (hAuxu : ∀ index, let d := aux131 index; InnerProductSpace.HarmonicOnNhd d.harmonic H)
variable (hAuxub : ∀ index, let d := aux131 index; ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
variable (hAuxside : ∀ index, let i := index; let d := aux131 index; ∀ q : ℚ, 0 < q → ∀ G : Set (Ωa index),
      MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall 1)] G → 0 < d.measure G →
      (∀ ω ∈ G, IsChangeConfigInc (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) →
      (∀ ω ∈ G, d.lifetime ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
        IsCfPocketConfig (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
            (d.curve ω)) →
      (∀ ω ∈ G, rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
            (d.curve ω)) →
      TwoSeedSideInput i.kappa i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall 1)) d.measure
          d.rightWall (d.leftWall 1) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)} (centredField
              d.translatedField d.coupledMean) d.harmonic ∧
        TwoSeedSideInputInf i.kappa i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall 1))
            d.measure d.rightWall (d.leftWall 1) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)} (centredField
              d.translatedField d.coupledMean) d.harmonic)
variable (auxFrame : Now.Extremal → Late.Frame)
variable (ΩAuxStage : Now.Extremal → Type) [mAuxStage : ∀ i, MeasurableSpace (ΩAuxStage i)]
variable (auxStageMeasure : ∀ i, Measure (ΩAuxStage i))
variable [hAuxStageProbability : ∀ i, IsProbabilityMeasure (auxStageMeasure i)]
variable (hAuxBounds : ∀ index, let i := index; IsFig51Bounds (16 / i.kappa) (auxFrame index).a (auxFrame index).b
      (auxFrame index).a' (auxFrame index).b')
variable (hAuxPiecewise : ∀ index, IsPiecewiseConstantBoundaryData (auxFrame index).boundary (auxFrame index).jumps)
variable (hAuxFlow : ∀ index, let i := index; let d := aux131 index; IsFlowLineDriver i.kappa (auxFrame
      index).boundary (auxFrame index).jumps 0 d.measure d.translatedField d.driver d.lifetime)
variable (hAuxWord : ∀ index, let i := index; ∀ x ∉ (auxFrame index).jumps ∪ Prop513Field.jumps (Real.exp (π *
      (auxFrame index).x₀)) (stripHJumps {0} {(auxFrame index).x₀}),
      (auxFrame index).boundary x = stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * (auxFrame index).x₀))
        (fig51Lower (auxFrame index).a (auxFrame index).b) (fig51Upper (auxFrame index).x₀ (auxFrame index).a'
            (auxFrame index).b') x)
variable (auxRoot : ∀ index, let i := index; let d := aux131 index; HistExp (16 / i.kappa) d.measure (auxStageMeasure
      index)
      (rootTgt d.driver (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
            i.kappa_gt_four (auxFrame index) (hAuxBounds index) d.translatedField))) treeTime))
      (fun _ => univ))
variable (hAuxReg0 : ∀ index, ∀ r : ℚ, 0 < r → IsRegFam ((auxRoot index).cand r))
variable (hAuxStart0 : ∀ index, ∀ r : ℚ, 0 < r → Measurable ((auxRoot index).y₀ r))
variable (hAuxEvent0 : ∀ index, ∀ r : ℚ, 0 < r → MeasurableSet[(auxRoot index).base r] ((auxRoot index).R₀ r))
variable (hAuxLaw0 : ∀ index, ∀ r : ℚ, 0 < r → Late.CandidateLaw (auxRoot index) r)
variable (auxNodes : ∀ index, let i := index; let d := aux131 index; ∀ n, HistExp (16 / i.kappa) d.measure
      (auxStageMeasure index)
      (nodeTgt d.driver (extremeAngleTreeDescendants (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
            i.kappa_gt_four (auxFrame index) (hAuxBounds index) d.translatedField)))
        treeTime descendantIndex n))
      (nodeAct (fun ω t => d.curve ω t) (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
            i.kappa_gt_four (auxFrame index) (hAuxBounds index) d.translatedField))) treeTime n)))
variable (hAuxReg : ∀ index, ∀ n, ∀ r : ℚ, 0 < r → IsRegFam (((auxNodes index) n).cand r))
variable (hAuxStart : ∀ index, ∀ n, ∀ r : ℚ, 0 < r → Measurable (((auxNodes index) n).y₀ r))
variable (hAuxEvent : ∀ index, ∀ n, ∀ r : ℚ, 0 < r → MeasurableSet[((auxNodes index) n).base r] (((auxNodes index)
      n).R₀ r))
variable (hAuxLaw : ∀ index, ∀ n, ∀ r : ℚ, 0 < r → Late.CandidateLaw ((auxNodes index) n) r)

variable (refFrame : BothLow → Frame)
variable (hRefBounds : ∀ index, IsFig51Bounds (16 / index.kappa) (refFrame index).a (refFrame index).b
      (refFrame index).a' (refFrame index).b')
variable (hRefWord : ∀ index, let x := word index; ∀ y ∉ counterflowJumps x.jumps ∪
      Prop513Field.jumps (Real.exp (π * (refFrame index).x₀)) (stripHJumps {0} {(refFrame index).x₀}),
      counterflowData (16 / index.kappa) x.boundary y = stripCounterflowData (16 / index.kappa) 0
        (Real.exp (π * (refFrame index).x₀)) (fig51Lower (refFrame index).a (refFrame index).b)
        (fig51Upper (refFrame index).x₀ (refFrame index).a' (refFrame index).b') y)
variable (ΩRefStage : BothLow → Type) [mRefStage : ∀ i, MeasurableSpace (ΩRefStage i)]
  [hRefStageBorel : ∀ i, StandardBorelSpace (ΩRefStage i)]
variable (refStageMeasure : ∀ i, Measure (ΩRefStage i))
variable [hRefStageProbability : ∀ i, IsProbabilityMeasure (refStageMeasure i)]
variable (refNoise₀ : ∀ index, ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ωw index → ℝ)
variable (refBase₀ : ∀ index, ℚ → MeasurableSpace (Ωw index × ΩRefStage index))
variable (hRefBase₀ : ∀ index q, refBase₀ index q ≤ (inferInstance : MeasurableSpace (Ωw index × ΩRefStage index)))
variable (hRefLaw₀ : ∀ index, let hP := fig51Source (16 / index.kappa) (refFrame index).x₀ (counterflowObjects
      (hWordS index).counterflow).field;
      ∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFarK (16 / index.kappa) ((word index).measure.prod (refStageMeasure index))
          (canonQ ((refBase₀ index) q) (rootCand (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3
          hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
          (hRefBounds index) (word index).measure hP (word index).driver (word index).lifetime (canonLam (word
          index).driver (word index).lifetime) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds
          index) (word index).driver (word index).lifetime) (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos
          index) (hRefBounds index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage
          index) q) ratGrid (rootNL_pos _) (rootNR_pos _) (rootStart (refFrame index).x₀ (sixteen_div_kappa_pos
          index) (hRefBounds index) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index)
          (word index).driver (word index).lifetime) (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos index)
          (hRefBounds index) (word index).driver (word index).lifetime) q) j t) (canonR (rootCand (refFrame index).x₀
          (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
          index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP (word index).driver
          (word index).lifetime (canonLam (word index).driver (word index).lifetime) (canonXL (refFrame index).x₀
          (sixteen_div_kappa_pos index) (hRefBounds index) (word index).driver (word index).lifetime) (canonXR
          (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word index).driver (word
          index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (canonXL (refFrame
          index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word index).driver (word index).lifetime)
          (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word index).driver (word
          index).lifetime) q) univ j t) (stageρL (16 / index.kappa) (rootρL (16 / index.kappa) (sourceWord (x₀ :=
          (refFrame index).x₀) (sixteen_div_kappa_pos index) (hRefBounds index))) j) (stageρR (16 / index.kappa)
          (rootρR (16 / index.kappa) (sourceWord (x₀ := (refFrame index).x₀) (sixteen_div_kappa_pos index)
          (hRefBounds index))) j) (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j))) (farR
          (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j))) (canonY (rootCand (refFrame index).x₀
          (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
          index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP (word index).driver
          (word index).lifetime (canonLam (word index).driver (word index).lifetime) (canonXL (refFrame index).x₀
          (sixteen_div_kappa_pos index) (hRefBounds index) (word index).driver (word index).lifetime) (canonXR
          (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word index).driver (word
          index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q) (rootStart (refFrame index).x₀
          (sixteen_div_kappa_pos index) (hRefBounds index) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index)
          (hRefBounds index) (word index).driver (word index).lifetime) (canonXR (refFrame index).x₀
          (sixteen_div_kappa_pos index) (hRefBounds index) (word index).driver (word index).lifetime) q) j t)
          (rootCand (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight
          hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word
          index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word
          index).lifetime) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word
          index).driver (word index).lifetime) (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds
          index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q j t).W
          (rootCand (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight
          hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word
          index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word
          index).lifetime) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word
          index).driver (word index).lifetime) (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds
          index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q j t).VL
          (rootCand (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight
          hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word
          index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word
          index).lifetime) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word
          index).driver (word index).lifetime) (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds
          index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q j t).VR
          (rootCand (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight
          hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word
          index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word
          index).lifetime) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word
          index).driver (word index).lifetime) (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds
          index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q j t).B
          (rootCand (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight
          hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word
          index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word
          index).lifetime) (canonXL (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) (word
          index).driver (word index).lifetime) (canonXR (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds
          index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q j t).ζ)
variable (refNoise : ∀ index, ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ωw index → ℝ)
variable (refBase : ∀ index, ℕ → ℚ → MeasurableSpace (Ωw index × ΩRefStage index))
variable (hRefBase : ∀ index n q, refBase index n q ≤ (inferInstance : MeasurableSpace (Ωw index × ΩRefStage index)))
variable (hRefLaw : ∀ index, let hP := fig51Source (16 / index.kappa) (refFrame index).x₀ (counterflowObjects (hWordS
      index).counterflow).field;
      ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ j t, IsStageLawFarK (16 / index.kappa) ((word index).measure.prod (refStageMeasure
          index)) (canonQ (nodeBase (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect)
          (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds
          index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index) (refBase index) n
          q) (nodeCand (Ωa := ΩRefStage index) (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3
          hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
          (hRefBounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index) n q)
          ratGrid (nodeNL_pos (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) n) (nodeNR_pos
          (refFrame index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) n) (nodeStart (refFrame index).x₀
          (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
          index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP (word index).driver
          (word index).lifetime (refNoise index) n q) j t) (canonR (nodeCand (Ωa := ΩRefStage index) (refFrame
          index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
          (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP
          (word index).driver (word index).lifetime (refNoise index) n q) ratGrid (nodeNL_pos (refFrame index).x₀
          (sixteen_div_kappa_pos index) (hRefBounds index) n) (nodeNR_pos (refFrame index).x₀ (sixteen_div_kappa_pos
          index) (hRefBounds index) n) (nodeStart (refFrame index).x₀ (late_theorem12ParamCond44Statement
          (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four
          index) (hRefBounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise
          index) n q) (nodeR0 (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect)
          (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds
          index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index) n q) j t)
          (stageρL (16 / index.kappa) (nodeρL (16 / index.kappa) (sourceWord (x₀ := (refFrame index).x₀)
          (sixteen_div_kappa_pos index) (hRefBounds index)) (scheduleAt n)) j) (stageρR (16 / index.kappa) (nodeρR
          (16 / index.kappa) (sourceWord (x₀ := (refFrame index).x₀) (sixteen_div_kappa_pos index) (hRefBounds
          index)) (scheduleAt n)) j) (farL (Nat.lt_of_lt_of_le (nodeNL_pos (refFrame index).x₀ (sixteen_div_kappa_pos
          index) (hRefBounds index) n) (Nat.le_add_right _ j))) (farR (Nat.lt_of_lt_of_le (nodeNR_pos (refFrame
          index).x₀ (sixteen_div_kappa_pos index) (hRefBounds index) n) (Nat.le_add_right _ j))) (canonY (nodeCand
          (Ωa := ΩRefStage index) (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect)
          (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds
          index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index) n q) (nodeStart
          (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
          (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP
          (word index).driver (word index).lifetime (refNoise index) n q) j t) (nodeCand (Ωa := ΩRefStage index)
          (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
          (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP
          (word index).driver (word index).lifetime (refNoise index) n q j t).W (nodeCand (Ωa := ΩRefStage index)
          (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
          (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP
          (word index).driver (word index).lifetime (refNoise index) n q j t).VL (nodeCand (Ωa := ΩRefStage index)
          (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
          (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP
          (word index).driver (word index).lifetime (refNoise index) n q j t).VR (nodeCand (Ωa := ΩRefStage index)
          (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
          (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP
          (word index).driver (word index).lifetime (refNoise index) n q j t).B (nodeCand (Ωa := ΩRefStage index)
          (refFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
          (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (hRefBounds index) (word index).measure hP
          (word index).driver (word index).lifetime (refNoise index) n q j t).ζ)

section

include hRect hRectEight hQ0 hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl
    hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hSwitched hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits refFrame hRefBounds hRefWord hRefStageBorel hRefStageProbability refNoise₀ refBase₀ hRefBase₀
    hRefLaw₀ refNoise refBase hRefBase hRefLaw

/-- **Lemma 7.25's determination reference from the pocket word's strip family, Proposition 5.13's experiments
constructed** (as `late_determinationReferenceFamily_strip`, through `late_pocketChartField_stripK`): besides the
pocket word's own binders, only the Figure 5.1 frame of each strip word and the killed laws of the concrete root and
node candidates (with their noise and past data) remain. -/
theorem late_determinationReferenceFamily_stripK : Aux50Hit.Lemma725DetReferenceStatement.{u} := by
  apply lemma725DetReferenceStatement_ulift.{0, u}
  apply Lemma725RefSafe.lemma725DetReferenceStatement_of_pocketChartField
  intro κ hκ rL rR hL hLd hR hRd
  let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have haux : Sec4.Aux7Statement.{0} i.kappa := by
    have hs : Sec4.Aux7Statement.{0} (16 / (16 / i.kappa)) :=
      Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA (hWordS i).kappa_pos (hWordS i).kappa_lt_four
    have heq : 16 / (16 / i.kappa) = i.kappa := by field_simp
    rw [← heq]
    exact @hs
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨-, -, hC, hu'⟩ := counterflowObjects_spec (hWordS i).counterflow
  let _ : IsProbabilityMeasure (Now.wordObjects i (word i) (hWordS i)).measure := by
    change IsProbabilityMeasure (word i).measure
    infer_instance
  have hside := late_pocketSideInput i (Now.wordObjects i (word i) (hWordS i)) (wordSide i)
    (by simpa only [Now.wordObjects, hdual] using hC)
    (by simpa only [Now.wordObjects, hdual] using hu')
    (hWordvα i).continuous (fun q => (hWordvL i q).continuous)
    (hSidepre i) (hSideFo i) (hSideRawReference i) (hSideLattice i)
    (hSideCollar i) (hSideProbes i) (hSideJointGerms i) (hSideVisits i)
  exact late_pocketChartField_stripK i (word i) (late_coreG3 hRect) (late_coreEight hRectEight) hQ0 haux h411
    hSwitched (hWordS i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i) (hWordr i) (hWordl i) (hWorde i)
    (hWordu₀ i) (hWordvα i) (hWordvL i) (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i)
    (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i) (hWordηtr i) (hWordu i) (hWordub i) hside
    (refFrame i) (hRefBounds i) (hRefWord i) (refNoise₀ i) (refBase₀ i) (hRefBase₀ i) (hRefLaw₀ i)
    (refNoise i) (refBase i) (hRefBase i) (hRefLaw i)

end

section

include hRect hRectEight hCover hAvoid hCover0 hAvoid0 hOuter hQ0 hAuxBorel hAuxProbability hAuxT' hAuxTr hAuxu₀
    hAuxh hAuxC hAuxu₀' hAuxX hAuxζ hAuxRc hAuxLc hAuxR0 hAuxL0 hAuxRm hAuxLm hAuxdetR hAuxdetL hAuxlocR hAuxlocL
    hAuxηm hAuxηc hAuxη0 hAuxR hAuxL hAuxne hAuxord hAuxtrace hAuxattach hAuxattachI hAuxu hAuxub hAuxside auxFrame
    hAuxStageProbability hAuxBounds hAuxPiecewise hAuxFlow hAuxWord auxRoot hAuxReg0 hAuxStart0 hAuxEvent0 hAuxLaw0
    auxNodes hAuxReg hAuxStart hAuxEvent hAuxLaw hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁
    hWordθ₂ hWordr hWordl hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0
    hWordηm hWordηtr hSwitched hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes
    hSideJointGerms hSideVisits hWord𝔥 refFrame hRefBounds hRefWord hRefStageBorel hRefStageProbability refNoise₀
    refBase₀ hRefBase₀ hRefLaw₀ refNoise refBase hRefBase hRefLaw

/-- **Theorem 1.2** (`Exist.Theorem12Statement.{u}`, the unchanged source conclusion): `Wire.theorem12Statement_late`
with the two GB8 crossing comparisons proved (`late_crossLeftK`, `late_crossRightK`) and its 59-binder reference block
and `hQ` replaced by the Figure 5.1 frame of the pocket word's strip words and the killed laws of the concrete root and
node candidates. -/
theorem theorem12Statement_stripMarksK : Exist.Theorem12Statement.{u} := by
  have hCrossLeft : Late.CrossLeftKStatement := late_crossLeftK
  have hCrossRight : Late.CrossRightKStatement := late_crossRightK
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  have h51 := late_prop51QStatement hA Ref hCover hAvoid
  apply theorem12Statement_current hA2 hA2' h47
    (Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg h51)
  · apply late_r7ReferenceFamily (Ωa := Ωa) (aux131 := aux131) (ΩAuxStage := ΩAuxStage)
      (auxStageMeasure := auxStageMeasure) <;> assumption
  · apply late_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · apply late_determinationReferenceFamily_stripK (Ωw := Ωw) (word := word) (wordSide := wordSide)
      (ΩRefStage := ΩRefStage) (refStageMeasure := refStageMeasure) <;> assumption

end

section

include hRect hRectEight hCover0 hAvoid0 hOuter hQ0 hAuxBorel hAuxProbability hAuxT' hAuxTr hAuxu₀ hAuxh hAuxC
    hAuxu₀' hAuxX hAuxζ hAuxRc hAuxLc hAuxR0 hAuxL0 hAuxRm hAuxLm hAuxdetR hAuxdetL hAuxlocR hAuxlocL hAuxηm hAuxηc
    hAuxη0 hAuxR hAuxL hAuxne hAuxord hAuxtrace hAuxattach hAuxattachI hAuxu hAuxub hAuxside auxFrame
    hAuxStageProbability hAuxBounds hAuxPiecewise hAuxFlow hAuxWord auxRoot hAuxReg0 hAuxStart0 hAuxEvent0 hAuxLaw0
    auxNodes hAuxReg hAuxStart hAuxEvent hAuxLaw hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁
    hWordθ₂ hWordr hWordl hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0
    hWordηm hWordηtr hSwitched hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes
    hSideJointGerms hSideVisits hWord𝔥

/-- **Theorem 1.3** (`Exist.Theorem13Statement.{u}`, the unchanged source conclusion): `Wire.theorem13Statement_late`
with the two GB8 crossing comparisons proved (`late_crossLeftK`, `late_crossRightK`); every other binder unchanged. -/
theorem theorem13Statement_stripMarksK : Exist.Theorem13Statement.{u} := by
  have hCrossLeft : Late.CrossLeftKStatement := late_crossLeftK
  have hCrossRight : Late.CrossRightKStatement := late_crossRightK
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' : ∀ κ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ :=
    late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA20 := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA20
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  apply theorem13Statement_current h470 h51
  · apply late_r7ReferenceFamily (Ωa := Ωa) (aux131 := aux131) (ΩAuxStage := ΩAuxStage)
      (auxStageMeasure := auxStageMeasure) <;> assumption
  · apply late_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · exact hA2
  · exact hA2'

end

end Expanded
end InteractingSLE.Sec7.StripMarks
