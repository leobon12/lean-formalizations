/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux29CorLate
import InteractingSLE.Spec.Sec7.Aux29CorMeas
import InteractingSLE.Spec.Sec7.Aux29CorCollar
import InteractingSLE.Spec.Sec5.WordSafeWire

/-! # The late pocket side input from the restricted collar

PROVE-T12-ASSEMBLE3 (collar rewire). `Wire.late_pocketSideInput` and `Wire.wordSafe_pocketWordEvolution` with the
late-side collar asked only off finite exceptional physical sets (`LateSideCollarExc`, the form PROVE-SIDE-COLLAR2's
collar concludes): every pocket shape goes through `Wire.late_sideLimits_offExc` (PROVE-AUX29-CORNER; Aux. 29 covers
the excluded prime ends). The extra inputs are the walls' and the counterflow's measurability in `ω` (for the
hitting measurability of the active complement) and the bounded harmonic mean.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm3

open Current Sec7 LocalSets WangWu WholeField StripWall StripSideHeightProb StripPocketPath
  Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling Sec7.Lemma71C Sec7.Lemma71I
  Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks Sec7.PocketWordAssembly Sec7.PocketSeedOpen
  Sec7.PocketUnionPt Sec7.PocketStop Sec7.PocketStopWallsFin Sec7.PocketStopMarked
  Sec7.PocketLeftFrontier Sec7.StripPocketConfig Sec7.PocketWordPerQ Sec7.PocketStopSide
  Sec7.PocketTraversal Sec7.PocketAdapt Sec7.PocketWordIn Sec7.Aux119Heights Sec7.PhaseSel
open Exist.Staged (IsRegularDriver)

/-- **`Wire.late_pocketSideInput` with the restricted collar** (`LateSideCollarExc`: Lemma R.5's comparison off finite
exceptional physical sets `X`): each of the four pocket shapes by `late_sideLimits_offExc` instead of
`late_sideLimits`; the hitting measurability of the active complement from
    `SideTest.measurable_activeCompl_of_ready`. -/
theorem late_pocketSideInput_offExc {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (side : SideTest Ω → Late.SideData Ω)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver
      d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ q ω, Continuous (d.leftWall q ω))
    (hSidepre : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, locPrefixSigma
        (refs.info i) target.event target.curve refs.level ≤ mΩ)
    (hSideFo : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i ω, ω ∈ target.event
        → IsOpen (H \ refs.sets i ω))
    (hSideRawReference : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i,
        PocketStopUnionLaw (refs.info i) target.measure target.event target.curve target.domain (refs.sets i)
            target.zeroField refs.level)
    (hSideLattice : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ q : ℝ≥0, ∀ᵐ ω
        ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ q t, Measurable fun ω => d.leftWall q ω t)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => d.curve ω u)
    (hu : InnerProductSpace.HarmonicOnNhd d.harmonic H) (hub : ∃ M : ℝ, ∀ z ∈ H, |d.harmonic z| ≤ M)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (hXfin : ∀ j q ω, (X j q ω).Finite)
    (hSideCollar : LateSideCollarExc i d side X)
    (hSideProbes : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ N : ℕ, ∀ᵐ ω
        ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
    (hSideJointGerms : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, ∀ᵐ ω
        ∂target.measure, ω ∈ target.event → ω ∈ refs.event i →
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
    (hSideVisits : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ᵐ ω
        ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)
    : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall q)] G → 0 < d.measure G →
      (∀ ω ∈ G, IsChangeConfigInc (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, d.lifetime ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) →
        IsCfPocketConfig (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
            (d.curve ω)) →
      (∀ ω ∈ G, rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q) (fun s : ℝ => d.driver s.toNNReal ω)
            (d.curve ω)) →
      PocketSideLimitInput0 (16 / i.kappa) i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall (d.leftWall
          q)) d.measure d.rightWall (d.leftWall q) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)} (centredField d.translatedField
              d.coupledMean) d.harmonic ∧
        PocketSideLimitInputInf0 (16 / i.kappa) i.leftWeight i.rightWeight (wallsSigma d.measure d.rightWall
            (d.leftWall q)) d.measure d.rightWall (d.leftWall q) (StripSys.rt q) d.curve
          {ω | ω ∈ G ∧ ¬ 0 < rightLo (d.rightWall ω) (d.leftWall q ω) (StripSys.rt q)} (centredField
              d.translatedField d.coupledMean) d.harmonic := by
  intro q hq G hG hPG hconf hζG hcfg hcfgI
  constructor
  · intro A hA hAG hPA ψ hJordan hPoint
    constructor
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, false, true⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      let _ : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfg ω (hAG hω).1 (hAG hω).2).isDrivenCurve (hJordan ω hω)).1
      exact late_sideLimits_offExc i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        hj (fun q => SideTest.measurable_activeCompl_of_ready (i := i) hj hRc (hLc _) hRm (hLm _) hηm q) hu hub
        (X j) (hXfin j) (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, false, false⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      let _ : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfg ω (hAG hω).1 (hAG hω).2).isDrivenCurve (hJordan ω hω)).1
      exact late_sideLimits_offExc i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        hj (fun q => SideTest.measurable_activeCompl_of_ready (i := i) hj hRc (hLc _) hRm (hLm _) hηm q) hu hub
        (X j) (hXfin j) (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)
  · intro A hA hAG hPA ψ hJordan hPoint
    constructor
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, true, true⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      let _ : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfgI ω (hAG hω).1 (le_antisymm (not_lt.1 (hAG hω).2) ((hconf ω (hAG
            hω).1).1.changeCorner_props.1.1))).isDrivenCurve (hJordan ω hω)).1
      exact late_sideLimits_offExc i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        hj (fun q => SideTest.measurable_activeCompl_of_ready (i := i) hj hRc (hLc _) hRm (hLm _) hηm q) hu hub
        (X j) (hXfin j) (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, true, false⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      let _ : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfgI ω (hAG hω).1 (le_antisymm (not_lt.1 (hAG hω).2) ((hconf ω (hAG
            hω).1).1.changeCorner_props.1.1))).isDrivenCurve (hJordan ω hω)).1
      exact late_sideLimits_offExc i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        hj (fun q => SideTest.measurable_activeCompl_of_ready (i := i) hj hRc (hLc _) hRm (hLm _) hηm q) hu hub
        (X j) (hXfin j) (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)


/-- **`Wire.wordSafe_pocketWordEvolution` with the restricted collar** (`late_pocketSideInput_offExc`). -/
theorem wordSafe_pocketWordEvolution_offExc {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
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
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) (hXfin : ∀ j q ω, (X j q ω).Finite)
    (hSideCollar : LateSideCollarExc i (wordSafeObjects i x hS) side X)
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
  have hside := late_pocketSideInput_offExc i d side
    (by simpa only [d, wordSafeObjects, hdual] using hC)
    (by simpa only [d, wordSafeObjects, hdual] using hu')
    hvα.continuous (fun q => (hvL q).continuous)
    hSidepre hSideFo hSideRawReference hSideLattice hvα.measurable (fun q => (hvL q).measurable) hηm hu hub X hXfin
    hSideCollar hSideProbes hSideJointGerms hSideVisits
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

end InteractingSLE.Wire.T12Asm3
