/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.WordSafeReg
import InteractingSLE.Spec.Wire.Thm12Night

/-!
# Theorems 1.2 and 1.3 at the Night frontier from two-angle strip systems

Packet PROVE-WORDSAFE. PROVE-WIRE-PARTA's Night wiring (`Thm12Night`, `Thm12NightPocket`, `Thm12LatePocket`)
with, for each both-low index, the supplied word objects required to form only a **two-angle strip system**
(`Sec7.WordSafe.IsTwoAngleStripSystem`, staged histories for the constant-angle and two-angle programs, which is all
the pocket word reads) instead of a full `StripSys.IsStripSystem`, and **without** the three every-sample driver
regularity inputs (the family is regularized inside the proof, `Sec7.WordSafe.regTwo`). Every other binder is
unchanged; the side-reference binders read the same word objects through `wordSafeObjects`, which is
`Now.wordObjects` with the two-angle system (`wordSafeObjects_toTwoAngle`: definitionally equal).

* `wordSafeObjects`, `wordSafe_switched` (the switched-wall law for two-angle systems, from the same inputs as
  `night_switched`);
* `wordSafe_pocketWordEvolution` (= `late_pocketWordEvolution`), `wordSafe_h513_of_stripSystem`
  (= `night_h513_of_stripSystem`), `wordSafe_pocketChartField` (= `night_pocketChartField`);
* `wordSafe_pocketWordFamily`, `wordSafe_determinationReferenceFamily`, **`theorem12Statement_wordSafe`**,
  **`theorem13Statement_wordSafe`** (= `theorem12Statement_night`, `theorem13Statement_night`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Function Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire

section

open Current Sec7 LocalSets WangWu WholeField StripWall StripSideHeightProb StripPocketPath
  Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I
  Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks Sec7.PocketWordAssembly Sec7.PocketSeedOpen
  Sec7.PocketUnionPt Sec7.PocketStop Sec7.PocketStopWallsFin Sec7.PocketStopMarked
  Sec7.PocketLeftFrontier Sec7.StripPocketConfig Sec7.PocketWordPerQ Sec7.PocketStopSide
  Sec7.PocketTraversal Sec7.PocketAdapt Sec7.PocketWordIn
open Exist.Staged (IsRegularDriver)

/-- `Now.wordObjects` for a two-angle strip system: the actual counterflow witness determines the data-only
side-test frame. -/
def wordSafeObjects {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
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

/-- `wordSafeObjects` of the two-angle system of a strip system is `Now.wordObjects` (the frame reads only the
counterflow witness). -/
theorem wordSafeObjects_toTwoAngle {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment) :
    wordSafeObjects i x hS.toTwoAngle = Now.wordObjects i x hS := rfl

end

section

/-- The switched-wall law for two-angle strip systems, from the inputs of `night_switched`. -/
theorem wordSafe_switched (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hChart : Sec5.CfGiven.CfGivenChartStatement.{u}) :
    Sec7.WordSafe.SwitchedWallFirstHitStatement.{u} := by
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  exact Sec7.WordSafe.switchedWallFirstHitStatement_of_input h47
    (fun θ hθ => late_lemma47QHitTStatement hA hθ.1 hθ.2)
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)
    (Sec5.CfGiven.counterflowGivenPrefixStatement_of_chart hChart)

end

section

open Current Sec7 LocalSets WangWu WholeField StripWall StripSideHeightProb StripPocketPath
  Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I
  Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks Sec7.PocketWordAssembly Sec7.PocketSeedOpen
  Sec7.PocketUnionPt Sec7.PocketStop Sec7.PocketStopWallsFin Sec7.PocketStopMarked
  Sec7.PocketLeftFrontier Sec7.StripPocketConfig Sec7.PocketWordPerQ Sec7.PocketStopSide
  Sec7.PocketTraversal Sec7.PocketAdapt Sec7.PocketWordIn
open Sec7.Aux119Heights Sec7.PhaseSel
open Exist.Staged (IsRegularDriver)

/-- `late_pocketWordEvolution` for a two-angle strip system, without the driver-regularity inputs. -/
theorem wordSafe_pocketWordEvolution {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (haux7 : Sec4.Aux7Statement.{0} i.kappa)
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (hsw : Sec7.WordSafe.SwitchedWallFirstHitStatement.{0})
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field x.driver x.lifetime
        x.experiment)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθ₁ : x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
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
    (hu : InnerProductSpace.HarmonicOnNhd x.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
    (side : SideTest Ω → Late.SideData Ω)
    (hSidepre : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤ mΩ)
    (hSideFo : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
    (hSideRawReference : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j;
            ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event target.curve target.domain (refs.sets i)
                target.zeroField refs.level)
    (hSideLattice : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
    (hSideCollar : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
            ∀ q : ℝ≥0, ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level) target.zeroField
          target.measure (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean ((activeCompl target.event target.curve target.baseChart) q)
          target.zeroField target.measure g →
      ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (activeCompl target.event target.curve target.baseChart) q
            ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (activeCompl target.event target.curve target.baseChart)
              q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve ω)
                q)
            (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve ω)
                q) →
            ∃ (i : ℕ) (b d : ℝ),
              let inv := (relChart target.baseChart target.curve q ω).2.1;
              let vB := harmRep (gB i ω) (H \ liveExt target.event target.curve target.domain (refs.sets i) refs.level
                  ω);
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
    (hSideProbes : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
    (hSideJointGerms : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j; ∀ i, ∀ᵐ ω ∂target.measure, ω ∈ target.event → ω ∈ refs.event i →
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
    (hSideVisits : let d := wordSafeObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d;
        let refs := side j; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)
    : Lemma725Ref.PocketWordEvolution.{0} i.kappa i.leftWeight i.rightWeight := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by
    field_simp
  let d := wordSafeObjects i x hS
  let _ : IsProbabilityMeasure d.measure := by
    change IsProbabilityMeasure x.measure
    infer_instance
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hside := late_pocketSideInput i d side
    (by simpa only [d, wordSafeObjects, hdual] using hC)
    (by simpa only [d, wordSafeObjects, hdual] using hu')
    hvα.continuous (fun q => (hvL q).continuous)
    hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits
  have hp := Sec7.WordSafe.pocketWordEvolution_of_twoAngle_restartGen h44
    (by rw [hdual]; exact haux7) h411 h47 hsw hS hleft hright hθ₁ hθ₂
    i.left_gt (by simpa only [hdual] using i.left_lt)
    i.right_gt (by simpa only [hdual] using i.right_lt)
    hu₀ hvα hvL hβc hβ0 hβm hβtr hηc hηH hη0 hηm hηtr
    x.mean hu hub h𝔥
    (by
      intro q hq G hG hPG hconf hζG hcfg hcfgI
      have hs := hside q hq G hG hPG hconf hζG hcfg hcfgI
      constructor
      · convert hs.1 using 1 <;> simp only [d, wordSafeObjects, hdual]
      · convert hs.2 using 1 <;> simp only [d, wordSafeObjects, hdual])
  simpa only [hdual] using hp


end

section

open Sec7 Sec7.StripMarks Sec7.PocketWordIn Sec7.StripSysField
open Sec5 Sec5.Prop513Bridge Sec5.StripRevVisit Sec7.AdmCode
open WholeField Restart Sec4 Exist.Staged Exist.StagedLaw
open Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target

/-- `night_h513_of_stripSystem` for a two-angle strip system. -/
theorem wordSafe_h513_of_stripSystem
    (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hFH : StagedPrefixFirstHitStatement.{0})
    {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / k) b J P h W ζ E) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (f : Frame) (hκ : 0 < 16 / k) (hκ4 : 16 / k < 4) (hb : IsFig51Bounds (16 / k) f.a f.b f.a' f.b')
    (hword : ∀ x ∉ counterflowJumps J ∪ Prop513Field.jumps (Real.exp (π * f.x₀)) (stripHJumps {0} {f.x₀}),
      counterflowData (16 / k) b x = stripCounterflowData (16 / k) 0 (Real.exp (π * f.x₀))
        (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') x)
    (hlaws : Hsd.Fig51CandLawsStatement h44)
    (u : ℂ → ℝ) :
    let d := counterflowObjects hS.counterflow
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField d.field d.mean ω + smoothDist upperHalfPlaneOpens u) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t := by
  intro d
  have hfl := Sec7.WordSafe.stripCounterflow_isFlowLineDriver hS
  have hbP := isPiecewiseConstant_counterflowData (16 / k) hS.boundaryData
  have hG := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
    (div_pos (by norm_num) hκ) hbP hfl
  have hGF := isStripGFF_parameterSource_of_word hκ hbP hG hword
  have hTF : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * f.x₀)))
      (-1) (-(π * chiC (16 / k))) (chiC (16 / (16 / k))) (fig51Source (16 / k) f.x₀ d.field ω) (d.field ω) :=
    fun ω => isChartTransport_parameterSource (Real.exp_pos _) _ _ (d.field ω)
  have hcf : IsStripCounterflowDriver (16 / k) 0 (Real.exp (π * f.x₀)) P
      (fig51Source (16 / k) f.x₀ d.field) W ζ := by
    refine ⟨counterflowData (16 / k) b, counterflowJumps J, d.field, hbP, ?_, hfl⟩
    simpa only [zero_add] using hTF
  have htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t : ℝ≥0 => η ω t) := by
    filter_upwards [hηtr, hS.lifetime] with ω hω hζ
    rw [hζ]
    exact hω
  rw [comap_centredField_add]
  obtain ⟨Γ', hm, he⟩ := Hsd.prop513_path_of_fig51CandLaws h44 hA hFH hlaws hκ hκ4 hb
    (𝒢 := MeasurableSpace.comap (fig51Source (16 / k) f.x₀ d.field) inferInstance) (comap_measurable _)
    hGF hcf htr
  refine ⟨Γ', ?_, he⟩
  intro t
  rw [← comap_eq_strip_parameter (Real.exp_pos _) hTF]
  exact hm t

open Current WangWu WholeField StripWall Sec7.PocketStopField Sec7.PocketStopWalls
open Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan
open Sec7.PocketMarks Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
open Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
open Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt

/-- `night_pocketChartField` for a two-angle strip system, without the driver-regularity inputs. -/
theorem wordSafe_pocketChartField {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hCore : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hCoreEight : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ)
    (hQ : FrameQ.QScheduleFirstHitStatement.{0})
    (haux7 : Sec4.Aux7Statement.{0} i.kappa)
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (hsw : Sec7.WordSafe.SwitchedWallFirstHitStatement.{0})
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field x.driver x.lifetime
      x.experiment)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθ₁ : x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
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
    (hu : InnerProductSpace.HarmonicOnNhd x.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
    (hside : let d := wordSafeObjects i x hS
      ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)] G →
      0 < d.measure G →
      (∀ ω ∈ G, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, d.lifetime ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
        IsCfPocketConfig (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
          (d.curve ω)) →
      (∀ ω ∈ G, rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
          (d.curve ω)) →
      PocketSideLimitInput0 (16 / i.kappa) i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall q))
          d.measure d.rightWall (d.leftWall q) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)}
          (centredField d.translatedField d.coupledMean) d.harmonic ∧
        PocketSideLimitInputInf0 (16 / i.kappa) i.leftWeight i.rightWeight
          (wallsSigma d.measure d.rightWall (d.leftWall q)) d.measure d.rightWall (d.leftWall q) (StripSys.rt q)
          d.curve {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)}
          (centredField d.translatedField d.coupledMean) d.harmonic)
    (f : Frame) (hb : IsFig51Bounds (16 / i.kappa) f.a f.b f.a' f.b')
    (hword : ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π * f.x₀)) (stripHJumps {0} {f.x₀}),
      counterflowData (16 / i.kappa) x.boundary y = stripCounterflowData (16 / i.kappa) 0 (Real.exp (π * f.x₀))
        (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') y)
    (hlaws : Hsd.Fig51CandLawsStatement (late_theorem12ParamCond44Statement hCore hCoreEight)) :
    Lemma725RefSafe.PocketChartFieldStatement.{0} i.kappa i.leftWeight i.rightWeight := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by
    field_simp
  have hA := late_partAInputs hCore hCoreEight
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := late_theorem12ParamCond44Statement hCore hCoreEight
  have hFH := FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  have h513 := wordSafe_h513_of_stripSystem h44 hA hFH hS hηtr f (sixteen_div_kappa_pos i)
    (sixteen_div_kappa_lt_four i) hb hword hlaws x.harmonic
  have hp := Sec7.WordSafe.pocketChartFieldStatement_of_twoAngle_restartGen h44
    (by rw [hdual]; exact haux7) h411 h47 hsw hS hleft hright hθ₁ hθ₂
    i.left_gt (by simpa only [hdual] using i.left_lt)
    i.right_gt (by simpa only [hdual] using i.right_lt)
    hu₀ hvα hvL hβc hβ0 hβm hβtr hηc hηH hη0 hηm hηtr hu hub
    (by
      intro q hq G hG hPG hconf hζG hcfg hcfgI
      have hs := hside q hq G hG hPG hconf hζG hcfg hcfgI
      constructor
      · convert hs.1 using 1 <;> simp only [wordSafeObjects, hdual]
      · convert hs.2 using 1 <;> simp only [wordSafeObjects, hdual])
    h513
  simpa only [hdual] using hp


end

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
variable (hWordT : ∀ i, let x := word i;
    Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field
      x.driver x.lifetime x.experiment)
variable (hWordleft : ∀ i, let x := word i; ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
variable (hWordright : ∀ i, let x := word i; ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
variable (hWordθ₁ : ∀ i, let x := word i; x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
variable (hWordθ₂ : ∀ i, let x := word i; x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
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
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤
        (mWord index))
variable (hSideFo : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
variable (hSideRawReference : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event
        target.curve target.domain (refs.sets i) target.zeroField refs.level)
variable (hSideLattice : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife
        (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
variable (hSideCollar : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
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
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
variable (hSideJointGerms : ∀ index, let i := index; let x := word index;
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
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
    let d := wordSafeObjects i x (hWordT index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index) j; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)

variable (hRefWord : ∀ index, let x := word index; ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)

section
include hField hSeed hQ0 hChart0 hLaws hRefWord hWordBorel hWordProbability hWordT hWordleft hWordright hWordθ₁ hWordθ₂
  hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits

/-- `night_determinationReferenceFamily` from two-angle strip systems, without the driver-regularity inputs. -/
theorem wordSafe_determinationReferenceFamily : Aux50Hit.Lemma725DetReferenceStatement.{u} := by
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
  exact wordSafe_pocketChartField i (word i) (late_coreG3 (night_rectG3 hField)) (late_coreEight (night_rectEight
      hSeed))
    hQ0 haux h411
    (wordSafe_switched hA hChart0) (hWordT i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i)
    (hWordu₀ i) (hWordvα i) (hWordvL i) (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i)
    (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i) (hWordηtr i) (hWordu i) (hWordub i) hside
    (aux130RefFrame i) (aux130RefFrame_bounds i) (hRefWord i) hLaws

end

section
include hField hSeed hChart0 hWordBorel hWordProbability hWordT hWordleft hWordright hWordθ₁ hWordθ₂
    hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hWordu hWordub hWord𝔥 hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits

/-- `late_pocketWordFamily` from two-angle strip systems, without the driver-regularity inputs: the strip-source
hypotheses supply the entire both-low pocket-word family. -/
theorem wordSafe_pocketWordFamily : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 →
    -2 < rR → rR < κ / 2 - 4 → Lemma725Ref.PocketWordEvolution.{0} κ rL rR := by
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 (night_rectG3 hField))
  have hA2' := late_threeForceCrosscutEightStatement (late_coreEight (night_rectEight hSeed))
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

section
include hDy hRetarget hRefWord hWord𝔥 hField hSeed hDy0 hRetarget0 hQ0 hChart0 hLaws hMeans hOuter hWordBorel
  hWordProbability hWordT hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr
      hWordηc hWordηH hWordη0 hWordηm hWordηtr
    hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits

/-- `theorem12Statement_night` from two-angle strip systems, without the driver-regularity inputs. -/
theorem theorem12Statement_wordSafe : Exist.Theorem12Statement.{u} := by
  have hRect := night_rectG3 hField
  have hRectEight := night_rectEight hSeed
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA20 := late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hSwitched := wordSafe_switched hA hChart0
  have hCrossLeft : Late.CrossLeftKStatement := late_crossLeftK
  have hCrossRight : Late.CrossRightKStatement := late_crossRightK
  have hR7 := night_r7Reference hRect hRectEight hDy0 hRetarget0 hQ0 hLaws hMeans hOuter
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  have h51 := night_prop51 hA hDy hRetarget
  apply theorem12Statement_current hA2 hA20 h47
    (Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg h51) hR7
  · apply wordSafe_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · apply wordSafe_determinationReferenceFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
end

section
include hWord𝔥 hField hSeed hDy0 hRetarget0 hQ0 hChart0 hLaws hMeans hOuter hWordBorel hWordProbability hWordT hWordleft
  hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm
      hWordηtr
    hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms
    hSideVisits

/-- `theorem13Statement_night` from two-angle strip systems, without the driver-regularity inputs. -/
theorem theorem13Statement_wordSafe : Exist.Theorem13Statement.{u} := by
  have hRect := night_rectG3 hField
  have hRectEight := night_rectEight hSeed
  have hA2 := late_fourForceCrosscutG3LifeStatement (late_coreG3 hRect)
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have hSwitched := wordSafe_switched hA hChart0
  have hCrossLeft : Late.CrossLeftKStatement := late_crossLeftK
  have hCrossRight : Late.CrossRightKStatement := late_crossRightK
  have hR7 := night_r7Reference hRect hRectEight hDy0 hRetarget0 hQ0 hLaws hMeans hOuter
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h51 := night_prop51 hA hDy0 hRetarget0
  apply theorem13Statement_current h47 h51 hR7
  · apply wordSafe_pocketWordFamily (Ωw := Ωw) (word := word) (wordSide := wordSide) <;> assumption
  · exact hA2
  · exact late_threeForceCrosscutEightStatement (late_coreEight hRectEight)
end


end InteractingSLE.Wire
