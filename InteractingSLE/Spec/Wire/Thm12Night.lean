/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightPocket
import InteractingSLE.Spec.Wire.Thm12NightR7

/-!
# Theorems 1.2 and 1.3 at the Night frontier

PROVE-WIRE-PARTA. The RefFrameTop/StripMarksTopK strip words are retained.
R.7 uses its constant-strip, phase-means and Figure 5.1 determination reductions;
Lemma 7.25 shares the same killed-law input. All hypotheses below are named.
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
    (hField : ∀ κ, ZhanGT4.A1Patch.A1DualCouplingG3FieldStatement κ)
    (hSeed : ∀ κ, ZhanGT4.A1EightSeed.A1DualCouplingEightSeedMStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{u})
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget0 : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{0})
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hChart0 : Sec5.CfGiven.CfGivenChartStatement.{0})
    (hLaws : Hsd.Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 (night_rectG3 hField))
        (late_coreEight (night_rectEight hSeed))))
    (hMeans : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseSide.R7PhaseMeansRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuter : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → OuterPocketCompletion.{0} k rL rR)

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

variable (hRefWord : ∀ index, let x := word index; ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)

section
include hField hSeed hQ0 hChart0 hLaws hRefWord hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂
  hWordr hWordl
    hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits

/-- Lemma 7.25 with the fixed Aux. 130 frame and the shared killed-law input. -/
theorem night_determinationReferenceFamily : Aux50Hit.Lemma725DetReferenceStatement.{u} := by
  apply lemma725DetReferenceStatement_ulift.{0, u}
  apply Lemma725RefSafe.lemma725DetReferenceStatement_of_pocketChartField
  intro κ hκ rL rR hL hLd hR hRd
  let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 (night_rectG3 hField))
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight (night_rectEight hSeed))
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
  exact night_pocketChartField i (word i) (late_coreG3 (night_rectG3 hField)) (late_coreEight (night_rectEight hSeed))
    hQ0 haux h411
    (night_switched hA hChart0) (hWordS i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i) (hWordr i) (hWordl i)
      (hWorde i)
    (hWordu₀ i) (hWordvα i) (hWordvL i) (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i)
    (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i) (hWordηtr i) (hWordu i) (hWordub i) hside
    (aux130RefFrame i) (aux130RefFrame_bounds i) (hRefWord i) hLaws

end

section
include hDy hRetarget hRefWord hWord𝔥 hField hSeed hDy0 hRetarget0 hQ0 hChart0 hLaws hMeans hOuter hWordBorel
  hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl
    hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits

/-- Theorem 1.2, with every currently assembled input supplied. -/
theorem theorem12Statement_night : Exist.Theorem12Statement.{u} := by
  have hRect := night_rectG3 hField
  have hRectEight := night_rectEight hSeed
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA20 := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hSwitched := night_switched hA hChart0
  have hCrossLeft : Late.CrossLeftKStatement := late_crossLeftK
  have hCrossRight : Late.CrossRightKStatement := late_crossRightK
  have hR7 := night_r7Reference hRect hRectEight hDy0 hRetarget0 hQ0 hLaws hMeans hOuter
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  have h51 := night_prop51 hA hDy hRetarget
  apply theorem12Statement_current hA2 hA20 h47
    (Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg h51) hR7
  · apply late_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · apply night_determinationReferenceFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
end

section
include hWord𝔥 hField hSeed hDy0 hRetarget0 hQ0 hChart0 hLaws hMeans hOuter hWordBorel hWordProbability hWordS hWordleft
  hWordright hWordθ₁ hWordθ₂ hWordr hWordl
    hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits

/-- Theorem 1.3 at the same frontier; no universe-u fibre cover or Figure 5.1
word identity is required for its conclusion. -/
theorem theorem13Statement_night : Exist.Theorem13Statement.{u} := by
  have hRect := night_rectG3 hField
  have hRectEight := night_rectEight hSeed
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hSwitched := night_switched hA hChart0
  have hCrossLeft : Late.CrossLeftKStatement := late_crossLeftK
  have hCrossRight : Late.CrossRightKStatement := late_crossRightK
  have hR7 := night_r7Reference hRect hRectEight hDy0 hRetarget0 hQ0 hLaws hMeans hOuter
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h51 := night_prop51 hA hDy0 hRetarget0
  apply theorem13Statement_current h47 h51 hR7
  · apply late_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · exact hA2
  · exact late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
end

end InteractingSLE.Wire
