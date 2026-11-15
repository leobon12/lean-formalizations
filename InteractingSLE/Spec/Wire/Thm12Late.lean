/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LatePocket
import InteractingSLE.Spec.Wire.Thm12LateR7
import InteractingSLE.Spec.Wire.Thm12LateReference
import InteractingSLE.Spec.Sec5.RestartGenPocket
import InteractingSLE.Spec.Wire.Thm12Current

/-! # Theorems 1.2 and 1.3 after A.2 and the target-component corollary

All residual laws and source data are named. Part A and Lemma 4.7 come from the
A.1 rectangle cores. Corrected reference fibres supply E1. The pocket-word visits
come from the switched-wall restart law. Actual reference initialization remains
explicit where the source frame has not been identified.
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

open Current Sec7 LocalSets WangWu WholeField StripWall Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt
  Sec7.RefWire Sec7.PocketWordIn
open Sec7.Aux119Heights Sec7.PhaseSel
open Exist.Staged (IsRegularDriver)
open Sec4 Sec5 Sec5.Prop513Schedule Sec5.Prop513Target Sec5.Prop513TreeExtract Sec5.Prop513Asm
  Sec5.Prop59Sched Sec5.Prop59Stage Sec5.Prop59System Sec5.StripRevVisit Sec5.Prop59Nodes
open Restart Exist Exist.Staged Exist.StagedLaw

section Expanded

variable
    (hCrossLeft : Late.CrossLeftKStatement) (hCrossRight : Late.CrossRightKStatement)
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
    (hQ : Sec5.FrameQ.QScheduleFirstHitStatement.{u})
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hSwitched : Sec5.RestartGen.SwitchedWallFirstHitStatement.{0})
    (hOuter : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{0} κ rL rR)

variable (Ωw : BothLow → Type) [mWord : ∀ i, MeasurableSpace (Ωw i)]
    [hWordBorel : ∀ i, StandardBorelSpace (Ωw i)]
    (word : ∀ i, Now.StripObjects (Ωw i)) [hWordProbability : ∀ i, IsProbabilityMeasure (word i).measure]
    (wordSide : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i))
variable (hWordS : ∀ i, let x := word i; StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field x.driver x.lifetime x.experiment)
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
variable (hWordvα : ∀ i, let x := word i; IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1 x.rightWall)
variable (hWordvL : ∀ i, let x := word i; ∀ q, IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
variable (hWordβc : ∀ i, let x := word i; ∀ ω, Continuous (x.outerWall ω))
variable (hWordβ0 : ∀ i, let x := word i; ∀ ω, x.outerWall ω 0 = 0)
variable (hWordβm : ∀ i, let x := word i; ∀ t, Measurable fun ω => x.outerWall ω t)
variable (hWordβtr : ∀ i, let x := word i; ∀ᵐ ω ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec 0 ω).1 ⊤ (x.outerWall ω))
variable (hWordηc : ∀ i, let x := word i; ∀ ω, ContinuousOn (x.curve ω) (Ici 0))
variable (hWordηH : ∀ i, let x := word i; ∀ ω, ∀ t : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
variable (hWordη0 : ∀ i, let x := word i; ∀ ω, x.curve ω 0 = 0)
variable (hWordηm : ∀ i, let x := word i; ∀ t : ℝ, 0 ≤ t → Measurable fun ω => x.curve ω t)
variable (hWordηtr : ∀ i, let x := word i; ∀ᵐ ω ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0 => x.curve ω t))
variable (hWordu : ∀ i, let x := word i; InnerProductSpace.HarmonicOnNhd x.harmonic H)
variable (hWordub : ∀ i, let x := word i; ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
variable (hWord𝔥 : ∀ i, let x := word i; ∀ φ : TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
variable (hSidepre : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤ (mWord index))
variable (hSideFo : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
variable (hSideRawReference : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event target.curve target.domain (refs.sets i) target.zeroField refs.level)
variable (hSideLattice : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
variable (hSideCollar : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀ gB : ℕ → (Ωw index) → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level) target.zeroField target.measure (gB i)) →
      ∀ g : (Ωw index) → DistOn upperHalfPlaneOpens, IsLocalSetMean ((activeCompl target.event target.curve target.baseChart) q) target.zeroField target.measure g →
      ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve target.baseChart) q ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (activeCompl target.event target.curve target.baseChart) q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve ω) q)
            (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve ω) q) →
            ∃ (i : ℕ) (b d : ℝ),
              let inv := (relChart target.baseChart target.curve q ω).2.1;
              let vB := harmRep (gB i ω) (H \ liveExt target.event target.curve target.domain (refs.sets i) refs.level ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + target.harmonic (inv y) + chiC target.kappa * refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) - refs.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
                (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve ω) q)
                (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve ω) q)
                ξ + refs.phase q ω * (Ioo
                  (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                    zL q ω - segDriver (target.curve ω) q)
                  (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                    zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - refs.offset)
variable (hSideProbes : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
variable (hSideJointGerms : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; ∀ i, ∀ᵐ ω ∂target.measure, ω ∈ target.event → ω ∈ refs.event i →
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
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d; let refs := (wordSide index) j; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)

variable (Ωr : BothLow → Type u) [mRef : ∀ i, MeasurableSpace (Ωr i)]
    [hRefBorel : ∀ i, StandardBorelSpace (Ωr i)]
    (reference : ∀ i, Now.ReferenceObjects (Ωr i)) [hRefProbability : ∀ i, IsProbabilityMeasure (reference i).measure]
variable (hRefT' : ∀ index, let i := index; let d := reference index; ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω) (d.chartField ω))
variable (hRefTr : ∀ index, let i := index; let d := reference index; ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
variable (hRefu₀ : ∀ index, let i := index; let d := reference index; InnerProductSpace.HarmonicOnNhd d.originalMean H)
variable (hRefh : ∀ index, let i := index; let d := reference index; LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
variable (hRefC : ∀ index, let i := index; let d := reference index; IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
variable (hRefu₀' : ∀ index, let i := index; let d := reference index; IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean)
variable (hRefX : ∀ index, let i := index; let d := reference index; IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
variable (hRefζ : ∀ index, let i := index; let d := reference index; ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
variable (hRefRm : ∀ index, let i := index; let d := reference index; ∀ t, Measurable fun ω => d.rightWall ω t)
variable (hRefLm : ∀ index, let i := index; let d := reference index; ∀ q t, Measurable fun ω => d.leftWall q ω t)
variable (hRefRc : ∀ index, let i := index; let d := reference index; ∀ ω, Continuous (d.rightWall ω))
variable (hRefLc : ∀ index, let i := index; let d := reference index; ∀ q ω, Continuous (d.leftWall q ω))
variable (hRefR0 : ∀ index, let i := index; let d := reference index; ∀ ω, d.rightWall ω 0 = 0)
variable (hRefL0 : ∀ index, let i := index; let d := reference index; ∀ q ω, d.leftWall q ω 0 = 0)
variable (hRefβm : ∀ index, let i := index; let d := reference index; ∀ t, Measurable fun ω => d.outerWall ω t)
variable (hRefηm : ∀ index, let i := index; let d := reference index; ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
variable (hRefηc : ∀ index, let i := index; let d := reference index; ∀ ω, ContinuousOn (d.curve ω) (Ici 0))
variable (hRefηH : ∀ index, let i := index; let d := reference index; ∀ ω, ∀ t : ℝ, 0 ≤ t → d.curve ω t ∈ Hbar)
variable (hRefη0 : ∀ index, let i := index; let d := reference index; ∀ ω, d.curve ω 0 = 0)
variable (hRefR : ∀ index, let i := index; let d := reference index; ∀ᵐ ω ∂d.measure, IsSimpleProper (d.rightWall ω) ∧ IsWallReverseVisit (d.rightWall ω) (d.curve ω) ∧ IsWallVisited (d.rightWall ω) (d.curve ω))
variable (hRefβ : ∀ index, let i := index; let d := reference index; ∀ᵐ ω ∂d.measure, IsSimpleProper (d.outerWall ω) ∧ IsWallReverseVisit (d.outerWall ω) (d.curve ω) ∧ IsWallVisited (d.outerWall ω) (d.curve ω))
variable (hRefLw : ∀ index, let i := index; let d := reference index; ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsSimpleProper (d.leftWall q ω) ∧ IsWallReverseVisit (d.leftWall q ω) (d.curve ω) ∧
      d.leftWall q ω (StripSys.rt q) = d.outerWall ω (StripSys.rt q))
variable (hRefnohit : ∀ index, let i := index; let d := reference index; ∀ᵐ ω ∂d.measure, ∀ t : ℝ, 0 < t → d.curve ω t ≠ 0)
variable (hReflate : ∀ index, let i := index; let d := reference index; ∀ᵐ ω ∂d.measure, ∀ N : ℝ≥0, ∃ t, N ≤ t ∧ d.outerWall ω t ∉ range (d.rightWall ω))
variable (hReftrace : ∀ index, let i := index; let d := reference index; ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) ∧
      Continuous (fun s : ℝ => d.driver s.toNNReal ω) ∧ d.driver 0 ω = 0)
variable (hRefav : ∀ index, let i := index; let d := reference index; ∀ᵐ ω ∂d.measure, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (d.curve ω q) ∉ leftSideOf (range (d.outerWall ω)))
variable (hRefattach : ∀ index, let i := index; let d := reference index; ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
        (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcL (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 1))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
variable (hRefattachI : ∀ index, let i := index; let d := reference index; ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
      rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖d.curve ω t‖) atTop atTop ∧ IsWallVisited (d.leftWall q ω) (d.curve ω) ∧
        Sec6.AttachmentConstancyInf (d.curve ω) (cfPocket (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
          (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) (cfArcLInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q))
          (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) 0)))
variable (hRefdetR : ∀ index, let i := index; let d := reference index; ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
variable (hRefdetL : ∀ index, let i := index; let d := reference index; ∀ q t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall q ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
variable (hReflocR : ∀ index, let i := index; let d := reference index; Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
variable (hReflocL : ∀ index, let i := index; let d := reference index; ∀ q, Sec6.IsEntranceHistoryLocal (d.leftWall q) (centredField d.field d.originalMean) d.measure)
variable (hRefu : ∀ index, let i := index; let d := reference index; InnerProductSpace.HarmonicOnNhd d.harmonic H)
variable (hRefub : ∀ index, let i := index; let d := reference index; ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
variable (hRefside : ∀ index, let i := index; let d := reference index; ∀ q : ℚ, 0 < q → ∀ G : Set (Ωr index), MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)] G → 0 < d.measure G →
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
variable (refFrame : BothLow → Late.Frame)
variable (ΩRefStage : BothLow → Type) [mRefStage : ∀ i, MeasurableSpace (ΩRefStage i)]
variable (refStageMeasure : ∀ i, Measure (ΩRefStage i))
variable [hRefStageProbability : ∀ i, IsProbabilityMeasure (refStageMeasure i)]
variable (hRefBounds : ∀ index, let i := index; let d := reference index; IsFig51Bounds (16 / i.kappa) (refFrame index).a (refFrame index).b (refFrame index).a' (refFrame index).b')
variable (hRefPiecewise : ∀ index, let i := index; let d := reference index; IsPiecewiseConstantBoundaryData (refFrame index).boundary (refFrame index).jumps)
variable (hRefFlow : ∀ index, let i := index; let d := reference index; IsFlowLineDriver i.kappa (refFrame index).boundary (refFrame index).jumps 0 d.measure d.translatedField d.driver d.lifetime)
variable (hRefWord : ∀ index, let i := index; let d := reference index; ∀ x ∉ (refFrame index).jumps ∪ Prop513Field.jumps (Real.exp (π * (refFrame index).x₀)) (stripHJumps {0} {(refFrame index).x₀}),
      (refFrame index).boundary x = stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * (refFrame index).x₀))
        (fig51Lower (refFrame index).a (refFrame index).b) (fig51Upper (refFrame index).x₀ (refFrame index).a' (refFrame index).b') x)
variable (refRoot : ∀ index, let i := index; let d := reference index; HistExp (16 / i.kappa) d.measure (refStageMeasure index)
      (rootTgt d.driver (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) i.kappa_gt_four (refFrame index) (hRefBounds index) d.translatedField))) treeTime))
      (fun _ => univ))
variable (hRefReg0 : ∀ index, let i := index; let d := reference index; ∀ r : ℚ, 0 < r → IsRegFam ((refRoot index).cand r))
variable (hRefStart0 : ∀ index, let i := index; let d := reference index; ∀ r : ℚ, 0 < r → Measurable ((refRoot index).y₀ r))
variable (hRefEvent0 : ∀ index, let i := index; let d := reference index; ∀ r : ℚ, 0 < r → MeasurableSet[(refRoot index).base r] ((refRoot index).R₀ r))
variable (hRefLaw0 : ∀ index, let i := index; let d := reference index; ∀ r : ℚ, 0 < r → Late.CandidateLaw (refRoot index) r)
variable (refNodes : ∀ index, let i := index; let d := reference index; ∀ n, HistExp (16 / i.kappa) d.measure (refStageMeasure index)
      (nodeTgt d.driver (extremeAngleTreeDescendants (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) i.kappa_gt_four (refFrame index) (hRefBounds index) d.translatedField)))
        treeTime descendantIndex n))
      (nodeAct (fun ω t => d.curve ω t) (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) i.kappa_gt_four (refFrame index) (hRefBounds index) d.translatedField))) treeTime n)))
variable (hRefReg : ∀ index, let i := index; let d := reference index; ∀ n, ∀ r : ℚ, 0 < r → IsRegFam (((refNodes index) n).cand r))
variable (hRefStart : ∀ index, let i := index; let d := reference index; ∀ n, ∀ r : ℚ, 0 < r → Measurable (((refNodes index) n).y₀ r))
variable (hRefEvent : ∀ index, let i := index; let d := reference index; ∀ n, ∀ r : ℚ, 0 < r → MeasurableSet[((refNodes index) n).base r] (((refNodes index) n).R₀ r))
variable (hRefLaw : ∀ index, let i := index; let d := reference index; ∀ n, ∀ r : ℚ, 0 < r → Late.CandidateLaw ((refNodes index) n) r)

variable (Ωa : Now.Extremal → Type) [mAux : ∀ i, MeasurableSpace (Ωa i)]
    [hAuxBorel : ∀ i, StandardBorelSpace (Ωa i)]
    (aux131 : ∀ i, Now.ReferenceObjects (Ωa i)) [hAuxProbability : ∀ i, IsProbabilityMeasure (aux131 i).measure]
variable (hAuxT' : ∀ index, let i := index; let d := aux131 index; ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant (d.field ω) (d.chartField ω))
variable (hAuxTr : ∀ index, let i := index; let d := aux131 index; ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
variable (hAuxu₀ : ∀ index, let i := index; let d := aux131 index; InnerProductSpace.HarmonicOnNhd d.originalMean H)
variable (hAuxh : ∀ index, let i := index; let d := aux131 index; IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
variable (hAuxC : ∀ index, let i := index; let d := aux131 index; IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
variable (hAuxu₀' : ∀ index, let i := index; let d := aux131 index; IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean)
variable (hAuxX : ∀ index, let i := index; let d := aux131 index; IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
variable (hAuxζ : ∀ index, let i := index; let d := aux131 index; ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
variable (hAuxRc : ∀ index, let i := index; let d := aux131 index; ∀ ω, Continuous (d.rightWall ω))
variable (hAuxLc : ∀ index, let i := index; let d := aux131 index; ∀ ω, Continuous ((d.leftWall 1) ω))
variable (hAuxR0 : ∀ index, let i := index; let d := aux131 index; ∀ ω, d.rightWall ω 0 = 0)
variable (hAuxL0 : ∀ index, let i := index; let d := aux131 index; ∀ ω, (d.leftWall 1) ω 0 = 0)
variable (hAuxRm : ∀ index, let i := index; let d := aux131 index; ∀ t, Measurable fun ω => d.rightWall ω t)
variable (hAuxLm : ∀ index, let i := index; let d := aux131 index; ∀ t, Measurable fun ω => (d.leftWall 1) ω t)
variable (hAuxdetR : ∀ index, let i := index; let d := aux131 index; ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
variable (hAuxdetL : ∀ index, let i := index; let d := aux131 index; ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (d.leftWall 1) ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω))
variable (hAuxlocR : ∀ index, let i := index; let d := aux131 index; Sec6.IsEntranceHistoryLocal d.rightWall (centredField d.field d.originalMean) d.measure)
variable (hAuxlocL : ∀ index, let i := index; let d := aux131 index; Sec6.IsEntranceHistoryLocal (d.leftWall 1) (centredField d.field d.originalMean) d.measure)
variable (hAuxηm : ∀ index, let i := index; let d := aux131 index; ∀ t : ℝ, 0 ≤ t → Measurable fun ω => d.curve ω t)
variable (hAuxηc : ∀ index, let i := index; let d := aux131 index; ∀ ω, ContinuousOn (d.curve ω) (Ici 0))
variable (hAuxη0 : ∀ index, let i := index; let d := aux131 index; ∀ ω, d.curve ω 0 = 0)
variable (hAuxR : ∀ index, let i := index; let d := aux131 index; ∀ᵐ ω ∂d.measure, IsSimpleProper (d.rightWall ω) ∧ IsWallReverseVisit (d.rightWall ω) (d.curve ω) ∧ IsWallVisited (d.rightWall ω) (d.curve ω))
variable (hAuxL : ∀ index, let i := index; let d := aux131 index; ∀ᵐ ω ∂d.measure, IsSimpleProper ((d.leftWall 1) ω) ∧ IsWallReverseVisit ((d.leftWall 1) ω) (d.curve ω))
variable (hAuxne : ∀ index, let i := index; let d := aux131 index; ∀ᵐ ω ∂d.measure, range ((d.leftWall 1) ω) ≠ range (d.rightWall ω))
variable (hAuxord : ∀ index, let i := index; let d := aux131 index; ∀ᵐ ω ∂d.measure, Disjoint (range (d.rightWall ω)) (leftSideOf (range ((d.leftWall 1) ω))))
variable (hAuxtrace : ∀ index, let i := index; let d := aux131 index; ∀ᵐ ω ∂d.measure, IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) ∧
      Continuous (fun s : ℝ => d.driver s.toNNReal ω) ∧ d.driver 0 ω = 0)
variable (hAuxattach : ∀ index, let i := index; let d := aux131 index; ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      0 < rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (d.curve ω) (cfPocket (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
        (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) (cfArcL (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 1))
        (firstHit (d.curve ω) (cfArcR (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 0)))
variable (hAuxattachI : ∀ index, let i := index; let d := aux131 index; ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂d.measure, IsChangeConfigInc (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) →
      rightLo (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) = 0 →
      Tendsto (fun t => ‖d.curve ω t‖) atTop atTop ∧ IsWallVisited ((d.leftWall 1) ω) (d.curve ω) ∧
        Sec6.AttachmentConstancyInf (d.curve ω) (cfPocket (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
          (cfArcRInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q)) (cfArcLInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q))
          (firstHit (d.curve ω) (cfArcRInf (d.rightWall ω) ((d.leftWall 1) ω) (StripSys.rt q) 0)))
variable (hAuxu : ∀ index, let i := index; let d := aux131 index; InnerProductSpace.HarmonicOnNhd d.harmonic H)
variable (hAuxub : ∀ index, let i := index; let d := aux131 index; ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
variable (hAuxside : ∀ index, let i := index; let d := aux131 index; ∀ q : ℚ, 0 < q → ∀ G : Set (Ωa index), MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall 1)] G → 0 < d.measure G →
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
variable (auxFrame : Now.Extremal → Late.Frame)
variable (ΩAuxStage : Now.Extremal → Type) [mAuxStage : ∀ i, MeasurableSpace (ΩAuxStage i)]
variable (auxStageMeasure : ∀ i, Measure (ΩAuxStage i))
variable [hAuxStageProbability : ∀ i, IsProbabilityMeasure (auxStageMeasure i)]
variable (hAuxBounds : ∀ index, let i := index; let d := aux131 index; IsFig51Bounds (16 / i.kappa) (auxFrame index).a (auxFrame index).b (auxFrame index).a' (auxFrame index).b')
variable (hAuxPiecewise : ∀ index, let i := index; let d := aux131 index; IsPiecewiseConstantBoundaryData (auxFrame index).boundary (auxFrame index).jumps)
variable (hAuxFlow : ∀ index, let i := index; let d := aux131 index; IsFlowLineDriver i.kappa (auxFrame index).boundary (auxFrame index).jumps 0 d.measure d.translatedField d.driver d.lifetime)
variable (hAuxWord : ∀ index, let i := index; let d := aux131 index; ∀ x ∉ (auxFrame index).jumps ∪ Prop513Field.jumps (Real.exp (π * (auxFrame index).x₀)) (stripHJumps {0} {(auxFrame index).x₀}),
      (auxFrame index).boundary x = stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * (auxFrame index).x₀))
        (fig51Lower (auxFrame index).a (auxFrame index).b) (fig51Upper (auxFrame index).x₀ (auxFrame index).a' (auxFrame index).b') x)
variable (auxRoot : ∀ index, let i := index; let d := aux131 index; HistExp (16 / i.kappa) d.measure (auxStageMeasure index)
      (rootTgt d.driver (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) i.kappa_gt_four (auxFrame index) (hAuxBounds index) d.translatedField))) treeTime))
      (fun _ => univ))
variable (hAuxReg0 : ∀ index, let i := index; let d := aux131 index; ∀ r : ℚ, 0 < r → IsRegFam ((auxRoot index).cand r))
variable (hAuxStart0 : ∀ index, let i := index; let d := aux131 index; ∀ r : ℚ, 0 < r → Measurable ((auxRoot index).y₀ r))
variable (hAuxEvent0 : ∀ index, let i := index; let d := aux131 index; ∀ r : ℚ, 0 < r → MeasurableSet[(auxRoot index).base r] ((auxRoot index).R₀ r))
variable (hAuxLaw0 : ∀ index, let i := index; let d := aux131 index; ∀ r : ℚ, 0 < r → Late.CandidateLaw (auxRoot index) r)
variable (auxNodes : ∀ index, let i := index; let d := aux131 index; ∀ n, HistExp (16 / i.kappa) d.measure (auxStageMeasure index)
      (nodeTgt d.driver (extremeAngleTreeDescendants (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) i.kappa_gt_four (auxFrame index) (hAuxBounds index) d.translatedField)))
        treeTime descendantIndex n))
      (nodeAct (fun ω t => d.curve ω t) (extremeAngleTreeNode (capacityTree (driverTree
        (Late.schedules (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) i.kappa_gt_four (auxFrame index) (hAuxBounds index) d.translatedField))) treeTime n)))
variable (hAuxReg : ∀ index, let i := index; let d := aux131 index; ∀ n, ∀ r : ℚ, 0 < r → IsRegFam (((auxNodes index) n).cand r))
variable (hAuxStart : ∀ index, let i := index; let d := aux131 index; ∀ n, ∀ r : ℚ, 0 < r → Measurable (((auxNodes index) n).y₀ r))
variable (hAuxEvent : ∀ index, let i := index; let d := aux131 index; ∀ n, ∀ r : ℚ, 0 < r → MeasurableSet[((auxNodes index) n).base r] (((auxNodes index) n).R₀ r))
variable (hAuxLaw : ∀ index, let i := index; let d := aux131 index; ∀ n, ∀ r : ℚ, 0 < r → Late.CandidateLaw ((auxNodes index) n) r)

section

include hRect hRectEight hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr hSwitched hWordu hWordub hWord𝔥 hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits

/-- The strip-source hypotheses supply the entire both-low pocket-word family. -/
theorem late_pocketWordFamily : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 →
    -2 < rR → rR < κ / 2 - 4 → Lemma725Ref.PocketWordEvolution.{0} κ rL rR := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h44 := Sec5.Prop513Asm.theorem12ParamCond44Statement_of_lemma47Q_of_A2 h470 hA2 hA2'
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  intro κ hκ rL rR hL hLd hR hRd
  let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
  have haux : Sec4.Aux7Statement.{0} i.kappa := by
    have hs : Sec4.Aux7Statement.{0} (16 / (16 / i.kappa)) :=
      Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA (hWordS i).kappa_pos (hWordS i).kappa_lt_four
    have heq : 16 / (16 / i.kappa) = i.kappa := by field_simp
    rw [← heq]
    exact @hs
  exact late_pocketWordEvolution i (word i) h44 haux h411 h470 hSwitched
    (hWordS i) (hWordleft i) (hWordright i) (hWordθ₁ i)
    (hWordθ₂ i) (hWordr i) (hWordl i) (hWorde i)
    (hWordu₀ i) (hWordvα i) (hWordvL i) (hWordβc i)
    (hWordβ0 i) (hWordβm i) (hWordβtr i) (hWordηc i)
    (hWordηH i) (hWordη0 i) (hWordηm i) (hWordηtr i)
    (hWordu i) (hWordub i) (hWord𝔥 i) (wordSide i)
    (hSidepre i)
    (hSideFo i)
    (hSideRawReference i)
    (hSideLattice i)
    (hSideCollar i)
    (hSideProbes i)
    (hSideJointGerms i)
    (hSideVisits i)

end

section

include hAuxBorel hAuxProbability hAuxT' hAuxTr hAuxu₀ hAuxh hAuxC hAuxu₀' hAuxX hAuxζ hAuxRc hAuxLc hAuxR0 hAuxL0 hAuxRm hAuxLm hAuxdetR hAuxdetL hAuxlocR hAuxlocL hAuxηm hAuxηc hAuxη0 hAuxR hAuxL hAuxne hAuxord hAuxtrace hAuxattach hAuxattachI hAuxu hAuxub hAuxside auxFrame hAuxStageProbability hAuxBounds hAuxPiecewise hAuxFlow hAuxWord auxRoot hAuxReg0 hAuxStart0 hAuxEvent0 hAuxLaw0 auxNodes hAuxReg hAuxStart hAuxEvent hAuxLaw hRect hRectEight hQ0 hCrossLeft hCrossRight

/-- Aux. 131 uses the per-seed marked-stop producer, with its record constructed. -/
theorem late_aux131Family : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    max rL rR = κ / 2 - 4 → R7Pocket.R7PocketStopStatement.{0} κ rL rR R7Aux131.GoodR7 := by
  intro κ hκ rL rR hL hR hmax
  let i : Now.Extremal := ⟨κ, rL, rR, hκ, hL, hR, hmax⟩
  exact now_r7PocketStopStatement i (aux131 i)
    (hAuxT' i) (hAuxTr i) (hAuxu₀ i) (hAuxh i)
    (hAuxC i) (hAuxu₀' i) (hAuxX i) (hAuxζ i)
    (hAuxRc i) (hAuxLc i) (hAuxR0 i) (hAuxL0 i)
    (hAuxRm i) (hAuxLm i) (hAuxdetR i) (hAuxdetL i)
    (hAuxlocR i) (hAuxlocL i) (hAuxηm i) (hAuxηc i)
    (hAuxη0 i) (hAuxR i) (hAuxL i) (hAuxne i)
    (hAuxord i) (hAuxtrace i) (hAuxattach i) (hAuxattachI i)
    (hAuxu i) (hAuxub i) (hAuxside i) (late_reference513 hCrossLeft hCrossRight (late_coreG3 hRect) (late_coreEight hRectEight) hQ0 i.kappa_gt_four (aux131 i)
      (auxFrame i) (hAuxBounds i) (hAuxPiecewise i) (hAuxFlow i) (hAuxWord i)
      (hAuxζ i) ((hAuxtrace i).mono fun _ h => h.1)
      (auxRoot i) (hAuxReg0 i) (hAuxStart0 i) (hAuxEvent0 i) (hAuxLaw0 i)
      (auxNodes i) (hAuxReg i) (hAuxStart i) (hAuxEvent i) (hAuxLaw i))

end

section

include hRect hRectEight hCover0 hAvoid0 hOuter hAuxBorel hAuxProbability hAuxT' hAuxTr hAuxu₀ hAuxh hAuxC hAuxu₀' hAuxX hAuxζ hAuxRc hAuxLc hAuxR0 hAuxL0 hAuxRm hAuxLm hAuxdetR hAuxdetL hAuxlocR hAuxlocL hAuxηm hAuxηc hAuxη0 hAuxR hAuxL hAuxne hAuxord hAuxtrace hAuxattach hAuxattachI hAuxu hAuxub hAuxside auxFrame hAuxStageProbability hAuxBounds hAuxPiecewise hAuxFlow hAuxWord auxRoot hAuxReg0 hAuxStart0 hAuxEvent0 hAuxLaw0 auxNodes hAuxReg hAuxStart hAuxEvent hAuxLaw hQ0 hCrossLeft hCrossRight

/-- R.7 splits into the Aux. 131 reference and the residual outer-pocket construction.
The four outer arms, their order and avoidance are proved by R7Outer. -/
theorem late_r7ReferenceFamily : R7.R7ReferenceStatement.{0} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  apply RefWire.r7ReferenceStatement_of_extremal_outer_completion h411 h51
  · apply late_aux131Family (Ωa := Ωa) (aux131 := aux131) (ΩAuxStage := ΩAuxStage) (auxStageMeasure := auxStageMeasure) <;> assumption
  · exact hOuter

end

section

include hRefBorel hRefProbability hRefT' hRefTr hRefu₀ hRefh hRefC hRefu₀' hRefX hRefζ hRefRm hRefLm hRefRc hRefLc hRefR0 hRefL0 hRefβm hRefηm hRefηc hRefηH hRefη0 hRefR hRefβ hRefLw hRefnohit hReflate hReftrace hRefav hRefattach hRefattachI hRefdetR hRefdetL hReflocR hReflocL hRefu hRefub hRefside refFrame hRefStageProbability hRefBounds hRefPiecewise hRefFlow hRefWord refRoot hRefReg0 hRefStart0 hRefEvent0 hRefLaw0 refNodes hRefReg hRefStart hRefEvent hRefLaw hRect hRectEight hQ hCrossLeft hCrossRight

/-- The determination reference uses an independent record for each rational seed. -/
theorem late_determinationReferenceFamily : Aux50Hit.Lemma725DetReferenceStatement.{u} := by
  apply Lemma725RefSafe.lemma725DetReferenceStatement_of_pocketChartField
  intro κ hκ rL rR hL hLd hR hRd
  let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
  exact now_pocketChartFieldStatement i (reference i)
    (hRefT' i) (hRefTr i) (hRefu₀ i) (hRefh i)
    (hRefC i) (hRefu₀' i) (hRefX i) (hRefζ i)
    (hRefRm i) (hRefLm i) (hRefRc i) (hRefLc i)
    (hRefR0 i) (hRefL0 i) (hRefβm i) (hRefηm i)
    (hRefηc i) (hRefηH i) (hRefη0 i) (hRefR i)
    (hRefβ i) (hRefLw i) (hRefnohit i) (hReflate i)
    (hReftrace i) (hRefav i) (hRefattach i) (hRefattachI i)
    (hRefdetR i) (hRefdetL i) (hReflocR i) (hReflocL i)
    (hRefu i) (hRefub i) (hRefside i) (late_reference513 hCrossLeft hCrossRight (late_coreG3 hRect) (late_coreEight hRectEight) hQ i.kappa_gt_four (reference i)
      (refFrame i) (hRefBounds i) (hRefPiecewise i) (hRefFlow i) (hRefWord i)
      (hRefζ i) ((hReftrace i).mono fun _ h => h.1)
      (refRoot i) (hRefReg0 i) (hRefStart0 i) (hRefEvent0 i) (hRefLaw0 i)
      (refNodes i) (hRefReg i) (hRefStart i) (hRefEvent i) (hRefLaw i))

end

section

include hRect hRectEight hCover0 hAvoid0 hOuter hAuxBorel hAuxProbability hAuxT' hAuxTr hAuxu₀ hAuxh hAuxC hAuxu₀' hAuxX hAuxζ hAuxRc hAuxLc hAuxR0 hAuxL0 hAuxRm hAuxLm hAuxdetR hAuxdetL hAuxlocR hAuxlocL hAuxηm hAuxηc hAuxη0 hAuxR hAuxL hAuxne hAuxord hAuxtrace hAuxattach hAuxattachI hAuxu hAuxub hAuxside auxFrame hAuxStageProbability hAuxBounds hAuxPiecewise hAuxFlow hAuxWord auxRoot hAuxReg0 hAuxStart0 hAuxEvent0 hAuxLaw0 auxNodes hAuxReg hAuxStart hAuxEvent hAuxLaw hQ0 hCover hAvoid hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr hSwitched hWordu hWordub hWord𝔥 hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits hRefBorel hRefProbability hRefT' hRefTr hRefu₀ hRefh hRefC hRefu₀' hRefX hRefζ hRefRm hRefLm hRefRc hRefLc hRefR0 hRefL0 hRefβm hRefηm hRefηc hRefηH hRefη0 hRefR hRefβ hRefLw hRefnohit hReflate hReftrace hRefav hRefattach hRefattachI hRefdetR hRefdetL hReflocR hReflocL hRefu hRefub hRefside refFrame hRefStageProbability hRefBounds hRefPiecewise hRefFlow hRefWord refRoot hRefReg0 hRefStart0 hRefEvent0 hRefLaw0 refNodes hRefReg hRefStart hRefEvent hRefLaw hQ hCrossLeft hCrossRight

/-- Theorem 1.2 after the currently landed reductions. Remaining source laws,
reference phases, source determination and geometric comparison inputs are named. -/
theorem theorem12Statement_late : Exist.Theorem12Statement.{u} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2'
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  have h51 := late_prop51QStatement hA Ref hCover hAvoid
  apply theorem12Statement_current hA2 hA2' h47
    (Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg h51)
  · apply late_r7ReferenceFamily (Ωa := Ωa) (aux131 := aux131) (ΩAuxStage := ΩAuxStage) (auxStageMeasure := auxStageMeasure) <;> assumption
  · apply late_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · apply late_determinationReferenceFamily (Ωr := Ωr) (reference := reference) (ΩRefStage := ΩRefStage) (refStageMeasure := refStageMeasure) <;> assumption

end

section

include hRect hRectEight hCover0 hAvoid0 hOuter hAuxBorel hAuxProbability hAuxT' hAuxTr hAuxu₀ hAuxh hAuxC hAuxu₀' hAuxX hAuxζ hAuxRc hAuxLc hAuxR0 hAuxL0 hAuxRm hAuxLm hAuxdetR hAuxdetL hAuxlocR hAuxlocL hAuxηm hAuxηc hAuxη0 hAuxR hAuxL hAuxne hAuxord hAuxtrace hAuxattach hAuxattachI hAuxu hAuxub hAuxside auxFrame hAuxStageProbability hAuxBounds hAuxPiecewise hAuxFlow hAuxWord auxRoot hAuxReg0 hAuxStart0 hAuxEvent0 hAuxLaw0 auxNodes hAuxReg hAuxStart hAuxEvent hAuxLaw hQ0 hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr hSwitched hWordu hWordub hWord𝔥 hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits hCrossLeft hCrossRight

/-- Theorem 1.3 uses the same pocket and R.7 experiments; the determination
reference family and the general-universe Lemma 4.7/target inputs are unnecessary. -/
theorem theorem13Statement_late : Exist.Theorem13Statement.{u} := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA2' : ∀ κ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA20 := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA20
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h51 := late_prop51QStatement hA Ref0 hCover0 hAvoid0
  apply theorem13Statement_current h470 h51
  · apply late_r7ReferenceFamily (Ωa := Ωa) (aux131 := aux131) (ΩAuxStage := ΩAuxStage) (auxStageMeasure := auxStageMeasure) <;> assumption
  · apply late_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · exact hA2
  · exact hA2'

end

end Expanded
end InteractingSLE.Wire
