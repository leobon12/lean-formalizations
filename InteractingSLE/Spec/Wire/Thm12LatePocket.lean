/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12LateSide
import InteractingSLE.Spec.Wire.Thm12NowPocket
import InteractingSLE.Spec.Sec5.RestartGenPocket
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
open Sec7.Aux119Heights Sec7.PhaseSel
open Exist.Staged (IsRegularDriver)

/-- The pocket word from the switched restart law and the latest side-germ collector. -/
theorem late_pocketWordEvolution {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (haux7 : Sec4.Aux7Statement.{0} i.kappa)
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (hsw : Sec5.RestartGen.SwitchedWallFirstHitStatement.{0})
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
    (hu : InnerProductSpace.HarmonicOnNhd x.harmonic H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |x.harmonic z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
    (side : SideTest Ω → Late.SideData Ω)
    (hSidepre : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤ mΩ)
    (hSideFo : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
    (hSideRawReference : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event target.curve target.domain (refs.sets i) target.zeroField refs.level)
    (hSideLattice : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
    (hSideCollar : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (refs.sets i) refs.level) target.zeroField target.measure (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean ((activeCompl target.event target.curve target.baseChart) q) target.zeroField target.measure g →
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
    (hSideProbes : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
    (hSideJointGerms : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, ∀ᵐ ω ∂target.measure, ω ∈ target.event → ω ∈ refs.event i →
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
    (hSideVisits : let d := Now.wordObjects i x hS; ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)
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
  have hside := late_pocketSideInput i d side
    (by simpa only [d, Now.wordObjects, hdual] using hC)
    (by simpa only [d, Now.wordObjects, hdual] using hu')
    hvα.continuous (fun q => (hvL q).continuous)
    hSidepre hSideFo hSideRawReference hSideLattice hSideCollar hSideProbes hSideJointGerms hSideVisits
  have hp := pocketWordEvolution_of_stripSystem_restartGen h44
    (by rw [hdual]; exact haux7) h411 h47 hsw hS hleft hright hθ₁ hθ₂
    i.left_gt (by simpa only [hdual] using i.left_lt)
    i.right_gt (by simpa only [hdual] using i.right_lt)
    hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr hηc hηH hη0 hηm hηtr
    x.mean hu hub h𝔥
    (by
      intro q hq G hG hPG hconf hζG hcfg hcfgI
      have hs := hside q hq G hG hPG hconf hζG hcfg hcfgI
      constructor
      · convert hs.1 using 1 <;> simp only [d, Now.wordObjects, hdual]
      · convert hs.2 using 1 <;> simp only [d, Now.wordObjects, hdual])
  simpa only [hdual] using hp

end InteractingSLE.Wire
