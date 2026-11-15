/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripMarksTopK
import InteractingSLE.Spec.Sec7.RefFrame

/-!
# Theorem 1.2 with the strip words' Figure 5.1 frame fixed to Aux. lemma 130's heights

Packet PROVE-REFFRAME. `StripMarksTopK.theorem12Statement_stripMarksK` keeps, for each both-low pair `i`, a Figure 5.1
frame `refFrame i` of the strip word, its standing bounds `hRefBounds i`, and the Figure 5.1 identity `hRefWord i` of
the pocket word's strip word `word i`. Lemma 7.25's proof (p. 413) uses the strip coupling of Aux. lemma 130 (p. 408),
whose four heights are CHOSEN: "it suffices to take `a, b ≥ λ + πχ/2`, `a', b' ≥ λ + 3πχ/2`". Here:

* **`aux130RefFrame i`** `:= aux130Frame (16 / i.kappa)` (`RefFrame`: `x₀ = 0`, `a = b = λ + πχ/2`,
  `a' = b' = λ + 3πχ/2` at the flow parameter `16/κ'`) discharges `refFrame`;
* **`aux130RefFrame_bounds i`** (`isFig51Bounds_aux130Frame`) discharges `hRefBounds`;
* `hRefWord` remains, for this frame: a deterministic identity of the strip word `word i`, which holds when the strip
  system is built with the boundary data `(aux130RefFrame i).word (16 / i.kappa)` (`refWord_of_boundary_eq_aux130`).
  That boundary data satisfies the pocket word's height hypotheses `hWordleft`/`hWordright`
  (`aux130Frame_word_left/right`, the source's "substitution in (5.4)–(5.5)") and admits a strip system
  (`RefFrameExists.exists_isStripSystem_aux130Frame`);
* **`late_determinationReferenceFamily_refFrame`**, **`theorem12Statement_refFrame`**: Lemma 7.25's determination
  reference and Theorem 1.2 (unchanged conclusion `Exist.Theorem12Statement.{u}`) with `refFrame`, `hRefBounds`
  removed from the frontier (117 binders; `theorem12Statement_stripMarksK` has 119). The K-law leaves `hRefLaw₀`,
  `hRefLaw` now concern the fixed frame. Theorem 1.3's frontier never contained the frame.

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

/-- **The Figure 5.1 frame of the strip word of a both-low pair** (Lemma 7.25's proof, p. 413: the strip coupling of
Aux. lemma 130, p. 408): Aux. lemma 130's frame at the flow parameter `κ = 16/κ'`. -/
def aux130RefFrame (i : BothLow) : Frame := aux130Frame (16 / i.kappa)

/-- **The standing Figure 5.1 bounds of `aux130RefFrame`** (`hRefBounds` of `StripMarksTopK`). -/
theorem aux130RefFrame_bounds (i : BothLow) : IsFig51Bounds (16 / i.kappa) (aux130RefFrame i).a (aux130RefFrame i).b
    (aux130RefFrame i).a' (aux130RefFrame i).b' :=
  isFig51Bounds_aux130Frame (sixteen_div_kappa_pos i) (sixteen_div_kappa_lt_four i)

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

variable (hRefWord : ∀ index, let x := word index; ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)
variable (ΩRefStage : BothLow → Type) [mRefStage : ∀ i, MeasurableSpace (ΩRefStage i)]
  [hRefStageBorel : ∀ i, StandardBorelSpace (ΩRefStage i)]
variable (refStageMeasure : ∀ i, Measure (ΩRefStage i))
variable [hRefStageProbability : ∀ i, IsProbabilityMeasure (refStageMeasure i)]
variable (refNoise₀ : ∀ index, ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ωw index → ℝ)
variable (refBase₀ : ∀ index, ℚ → MeasurableSpace (Ωw index × ΩRefStage index))
variable (hRefBase₀ : ∀ index q, refBase₀ index q ≤ (inferInstance : MeasurableSpace (Ωw index × ΩRefStage index)))
variable (hRefLaw₀ : ∀ index, let hP := fig51Source (16 / index.kappa) (aux130RefFrame index).x₀ (counterflowObjects
      (hWordS index).counterflow).field; ∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFarK (16 / index.kappa) ((word
      index).measure.prod (refStageMeasure index)) (canonQ ((refBase₀ index) q) (rootCand (aux130RefFrame index).x₀
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
      index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word index).measure hP (word
      index).driver (word index).lifetime (canonLam (word index).driver (word index).lifetime) (canonXL
      (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word index).driver (word
      index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index)
      (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q) ratGrid (rootNL_pos _)
      (rootNR_pos _) (rootStart (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index)
      (canonXL (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word
      index).driver (word index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index)
      (aux130RefFrame_bounds index) (word index).driver (word index).lifetime) q) j t) (canonR (rootCand
      (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
      (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word
      index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word index).lifetime)
      (canonXL (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word
      index).driver (word index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index)
      (aux130RefFrame_bounds index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage
      index) q) ratGrid (rootNL_pos _) (rootNR_pos _) (rootStart (aux130RefFrame index).x₀ (sixteen_div_kappa_pos
      index) (aux130RefFrame_bounds index) (canonXL (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index)
      (aux130RefFrame_bounds index) (word index).driver (word index).lifetime) (canonXR (aux130RefFrame index).x₀
      (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word index).driver (word index).lifetime) q) univ j
      t) (stageρL (16 / index.kappa) (rootρL (16 / index.kappa) (sourceWord (x₀ := (aux130RefFrame index).x₀)
      (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index))) j) (stageρR (16 / index.kappa) (rootρR (16 /
      index.kappa) (sourceWord (x₀ := (aux130RefFrame index).x₀) (sixteen_div_kappa_pos index) (aux130RefFrame_bounds
      index))) j) (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j))) (farR (Nat.lt_of_lt_of_le
      (rootNR_pos _) (Nat.le_add_right _ j))) (canonY (rootCand (aux130RefFrame index).x₀
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
      index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word index).measure hP (word
      index).driver (word index).lifetime (canonLam (word index).driver (word index).lifetime) (canonXL
      (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word index).driver (word
      index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index)
      (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q) (rootStart
      (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (canonXL (aux130RefFrame
      index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word index).driver (word index).lifetime)
      (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word
      index).driver (word index).lifetime) q) j t) (rootCand (aux130RefFrame index).x₀
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
      index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word index).measure hP (word
      index).driver (word index).lifetime (canonLam (word index).driver (word index).lifetime) (canonXL
      (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word index).driver (word
      index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index)
      (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q j t).W (rootCand
      (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
      (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word
      index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word index).lifetime)
      (canonXL (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word
      index).driver (word index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index)
      (aux130RefFrame_bounds index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage
      index) q j t).VL (rootCand (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect)
      (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (canonLam (word
      index).driver (word index).lifetime) (canonXL (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index)
      (aux130RefFrame_bounds index) (word index).driver (word index).lifetime) (canonXR (aux130RefFrame index).x₀
      (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word index).driver (word index).lifetime)
      (refNoise₀ index) (Ωa := ΩRefStage index) q j t).VR (rootCand (aux130RefFrame index).x₀
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
      index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word index).measure hP (word
      index).driver (word index).lifetime (canonLam (word index).driver (word index).lifetime) (canonXL
      (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word index).driver (word
      index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index)
      (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage index) q j t).B (rootCand
      (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
      (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word
      index).measure hP (word index).driver (word index).lifetime (canonLam (word index).driver (word index).lifetime)
      (canonXL (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) (word
      index).driver (word index).lifetime) (canonXR (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index)
      (aux130RefFrame_bounds index) (word index).driver (word index).lifetime) (refNoise₀ index) (Ωa := ΩRefStage
      index) q j t).ζ)
variable (refNoise : ∀ index, ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ωw index → ℝ)
variable (refBase : ∀ index, ℕ → ℚ → MeasurableSpace (Ωw index × ΩRefStage index))
variable (hRefBase : ∀ index n q, refBase index n q ≤ (inferInstance : MeasurableSpace (Ωw index × ΩRefStage index)))
variable (hRefLaw : ∀ index, let hP := fig51Source (16 / index.kappa) (aux130RefFrame index).x₀ (counterflowObjects
      (hWordS index).counterflow).field; ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ j t, IsStageLawFarK (16 / index.kappa) ((word
      index).measure.prod (refStageMeasure index)) (canonQ (nodeBase (aux130RefFrame index).x₀
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos
      index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word index).measure hP (word
      index).driver (word index).lifetime (refNoise index) (refBase index) n q) (nodeCand (Ωa := ΩRefStage index)
      (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
      (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word
      index).measure hP (word index).driver (word index).lifetime (refNoise index) n q) ratGrid (nodeNL_pos
      (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) n) (nodeNR_pos
      (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) n) (nodeStart
      (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
      (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word
      index).measure hP (word index).driver (word index).lifetime (refNoise index) n q) j t) (canonR (nodeCand (Ωa :=
      ΩRefStage index) (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect)
      (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q) ratGrid (nodeNL_pos (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index)
      n) (nodeNR_pos (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) n)
      (nodeStart (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight
      hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word
      index).measure hP (word index).driver (word index).lifetime (refNoise index) n q) (nodeR0 (aux130RefFrame
      index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight))
      (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index) (aux130RefFrame_bounds index) (word
      index).measure hP (word index).driver (word index).lifetime (refNoise index) n q) j t) (stageρL (16 /
      index.kappa) (nodeρL (16 / index.kappa) (sourceWord (x₀ := (aux130RefFrame index).x₀) (sixteen_div_kappa_pos
      index) (aux130RefFrame_bounds index)) (scheduleAt n)) j) (stageρR (16 / index.kappa) (nodeρR (16 / index.kappa)
      (sourceWord (x₀ := (aux130RefFrame index).x₀) (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index))
      (scheduleAt n)) j) (farL (Nat.lt_of_lt_of_le (nodeNL_pos (aux130RefFrame index).x₀ (sixteen_div_kappa_pos index)
      (aux130RefFrame_bounds index) n) (Nat.le_add_right _ j))) (farR (Nat.lt_of_lt_of_le (nodeNR_pos (aux130RefFrame
      index).x₀ (sixteen_div_kappa_pos index) (aux130RefFrame_bounds index) n) (Nat.le_add_right _ j))) (canonY
      (nodeCand (Ωa := ΩRefStage index) (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3
      hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q) (nodeStart (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement (late_coreG3 hRect)
      (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q) j t) (nodeCand (Ωa := ΩRefStage index) (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement
      (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q j t).W (nodeCand (Ωa := ΩRefStage index) (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement
      (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q j t).VL (nodeCand (Ωa := ΩRefStage index) (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement
      (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q j t).VR (nodeCand (Ωa := ΩRefStage index) (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement
      (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q j t).B (nodeCand (Ωa := ΩRefStage index) (aux130RefFrame index).x₀ (late_theorem12ParamCond44Statement
      (late_coreG3 hRect) (late_coreEight hRectEight)) (sixteen_div_kappa_pos index) (sixteen_div_kappa_lt_four index)
      (aux130RefFrame_bounds index) (word index).measure hP (word index).driver (word index).lifetime (refNoise index)
      n q j t).ζ)

omit hWordBorel hWordProbability in
/-- **`hRefWord` for the strip word chosen with Aux. lemma 130's frame**: if each strip word's boundary data is
`(aux130RefFrame i).word (16 / i.kappa)` (the return data of the Figure 5.1 counterflow word), the Figure 5.1 identity
binder `hRefWord` holds (`Frame.refWord_of_boundary_eq`). -/
theorem refWord_of_boundary_eq_aux130
    (hb : ∀ i, (word i).boundary = (aux130RefFrame i).word (16 / i.kappa)) :
    ∀ index, let x := word index; ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y :=
  fun i => (aux130RefFrame i).refWord_of_boundary_eq _ _ (hb i)

section

include hRect hRectEight hQ0 hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl
    hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hSwitched hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits hRefWord hRefStageBorel hRefStageProbability refNoise₀ refBase₀ hRefBase₀ hRefLaw₀ refNoise refBase
    hRefBase hRefLaw

/-- **Lemma 7.25's determination reference with the strip words' frame fixed**
(`late_determinationReferenceFamily_stripK` with `refFrame := aux130RefFrame`,
`hRefBounds := aux130RefFrame_bounds`). -/
theorem late_determinationReferenceFamily_refFrame : Aux50Hit.Lemma725DetReferenceStatement.{u} := by
  apply late_determinationReferenceFamily_stripK (Ωw := Ωw) (word := word) (wordSide := wordSide)
    (ΩRefStage := ΩRefStage) (refStageMeasure := refStageMeasure) (refFrame := aux130RefFrame)
    (hRefBounds := aux130RefFrame_bounds) (refNoise₀ := refNoise₀) (refBase₀ := refBase₀) (refNoise := refNoise)
    (refBase := refBase) <;> assumption

end

section

include hRect hRectEight hCover hAvoid hCover0 hAvoid0 hOuter hQ0 hAuxBorel hAuxProbability hAuxT' hAuxTr hAuxu₀
    hAuxh hAuxC hAuxu₀' hAuxX hAuxζ hAuxRc hAuxLc hAuxR0 hAuxL0 hAuxRm hAuxLm hAuxdetR hAuxdetL hAuxlocR hAuxlocL
    hAuxηm hAuxηc hAuxη0 hAuxR hAuxL hAuxne hAuxord hAuxtrace hAuxattach hAuxattachI hAuxu hAuxub hAuxside auxFrame
    hAuxStageProbability hAuxBounds hAuxPiecewise hAuxFlow hAuxWord auxRoot hAuxReg0 hAuxStart0 hAuxEvent0 hAuxLaw0
    auxNodes hAuxReg hAuxStart hAuxEvent hAuxLaw hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁
    hWordθ₂ hWordr hWordl hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0
    hWordηm hWordηtr hSwitched hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes
    hSideJointGerms hSideVisits hWord𝔥 hRefWord hRefStageBorel hRefStageProbability refNoise₀ refBase₀ hRefBase₀
    hRefLaw₀ refNoise refBase hRefBase hRefLaw

/-- **Theorem 1.2** (`Exist.Theorem12Statement.{u}`, the unchanged source conclusion): `theorem12Statement_stripMarksK`
with the strip words' Figure 5.1 frame fixed to Aux. lemma 130's heights (`refFrame := aux130RefFrame`) and its
standing bounds proved (`hRefBounds := aux130RefFrame_bounds`); every other binder unchanged (`hRefWord`, `hRefLaw₀`,
`hRefLaw` for this frame). -/
theorem theorem12Statement_refFrame : Exist.Theorem12Statement.{u} := by
  apply theorem12Statement_stripMarksK (Ref := Ref) (Ref0 := Ref0) (Ωa := Ωa) (aux131 := aux131)
    (auxFrame := auxFrame) (ΩAuxStage := ΩAuxStage) (auxStageMeasure := auxStageMeasure) (auxRoot := auxRoot)
    (auxNodes := auxNodes) (Ωw := Ωw) (word := word) (wordSide := wordSide) (ΩRefStage := ΩRefStage)
    (refStageMeasure := refStageMeasure) (refFrame := aux130RefFrame) (hRefBounds := aux130RefFrame_bounds)
    (refNoise₀ := refNoise₀) (refBase₀ := refBase₀) (refNoise := refNoise) (refBase := refBase) <;> assumption

end

end Expanded
end InteractingSLE.Sec7.StripMarks
