/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NowSide
import InteractingSLE.Spec.Sec7.PocketSideInRef
import InteractingSLE.Spec.Sec7.PocketSideInAct
import InteractingSLE.Spec.Sec7.PocketSideInFaceCompare

/-! # Native side limits from the R73 reference germs and phase probes -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal
namespace InteractingSLE.Wire
open Current Sec7 LocalSets WangWu WholeField Sec7.PocketStopField Sec7.PocketStopWalls Sec7.PocketCoupling
  Sec7.Lemma71C Sec7.Lemma71I Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketMarks
  Sec7.PocketWordAssembly Sec7.PocketSeedOpen Sec7.PocketUnionPt Sec7.PocketStop
  Sec7.PocketStopWallsFin Sec7.PocketStopMarked Sec7.PocketLeftFrontier Sec7.StripPocketConfig
  Sec7.PocketWordPerQ Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PocketAdapt Sec7.Aux119Heights Sec7.PhaseSel
namespace Late

/-- Reference sets, lifts, phase probes and shared-face candidate data only. -/
structure SideData (Ω : Type) where
  level : ℝ≥0
  sets : ℕ → Ω → Set ℂ
  info : ℕ → MeasurableSpace Ω
  lift : ℕ → Ω → ℂ → ℝ
  phase : ℝ≥0 → Ω → ℝ
  offset : ℝ
  probe : ℕ → Ω → ℝ≥0 → ℝ
  baseProbe : ℕ → Ω → ℝ≥0 → ℝ
  weight : ℕ → Ω → ℝ≥0 → ℝ
  visit : ℚ → Ω → ℝ≥0
  event : ℚ → Set Ω
  currentMean : ℚ → Ω → ℂ → ℝ
  referenceMean : ℚ → Ω → ℂ → ℝ

def leftZero {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (j : SideTest Ω) : Fin (j.target i d).nL :=
  ⟨0, by cases hj : j.twoLeft <;> simp [SideTest.target, hj]⟩

def rightZero {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (j : SideTest Ω) : Fin (j.target i d).nR :=
  ⟨0, by cases hj : j.twoLeft <;> simp [SideTest.target, hj]⟩

end Late

/-- The latest reference-germ collector yields the unchanged native all-q side limit.
Reference means and locality, phase continuity and zero phase are proved internally. -/
theorem late_sideLimits {Ω : Type} [mΩ : MeasurableSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (j : SideTest Ω) (e : Late.SideData Ω)
    (hDriven : ∀ ω ∈ (j.target i d).event, IsDrivenCurve ((j.target i d).curve ω))
    (hOpen : ∀ ω ∈ (j.target i d).event, IsOpen ((j.target i d).domain ω))
    (hZero : IsZeroBoundaryGFF upperHalfPlaneOpens (j.target i d).zeroField (j.target i d).measure)
    (hpre : let target := j.target i d; ∀ i, locPrefixSigma (e.info i) target.event target.curve e.level ≤ mΩ)
    (hFo : let target := j.target i d; ∀ i ω, ω ∈ target.event → IsOpen (H \ e.sets i ω))
    (hRawReference : let target := j.target i d; ∀ i, PocketStopUnionLaw (e.info i) target.measure target.event target.curve target.domain (e.sets i) target.zeroField e.level)
    (hLattice : let target := j.target i d; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∃ m : ℤ, e.phase q ω = m * phaseStep target.kappa)
    (hCollar : let target := j.target i d; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt target.event target.curve target.domain (e.sets i) e.level) target.zeroField target.measure (gB i)) →
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
              let vB := harmRep (gB i ω) (H \ liveExt target.event target.curve target.domain (e.sets i) e.level ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + target.harmonic (inv y) + chiC target.kappa * e.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart target.baseChart target.curve q ω).2.2 (inv y) - e.lift i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + chiC target.kappa * d = forceBoundaryData target.kappa target.rhoL target.rhoR
                (fun i => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL i q ω - segDriver (target.curve ω) q)
                (fun j => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR j q ω - segDriver (target.curve ω) q)
                ξ + e.phase q ω * (Ioo
                  (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL
                    zL q ω - segDriver (target.curve ω) q)
                  (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR
                    zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - e.offset)
    (hProbes : let target := j.target i d; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (e.probe N ω) S ∧ ContinuousOn (e.baseProbe N ω) S ∧ ContinuousOn (e.weight N ω) S ∧
        ∀ t ∈ S, 0 < e.weight N ω t ∧ e.probe N ω t - e.baseProbe N ω t = e.phase t ω * e.weight N ω t)
    (hJointGerms : let target := j.target i d; ∀ i, ∀ᵐ ω ∂target.measure, ω ∈ target.event → ω ∈ e.event i →
      ∃ (ξ η y₀ : ℝ) (J : Set ℝ) (φ L : ℂ → ℂ) (bC bU b : ℝ),
        IsPreconnected J ∧ ξ ∈ J ∧ y₀ ∈ J ∧
        (∀ y ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal φ y r) ∧
        ContinuousOn (fun y : ℝ => L y) J ∧
        (∀ y ∈ J, Complex.exp (L y) = deriv (QuantumZipper.CA.schwarzReflect φ) y) ∧
        bC = bU ∧ bU = bC + chiC target.kappa * (L y₀).im ∧
        ContinuousWithinAt L Hbar (ξ : ℂ) ∧
        Tendsto φ (𝓝[H] (ξ : ℂ)) (𝓝[H] (η : ℂ)) ∧
        Tendsto (e.currentMean i ω) (𝓝[H] (ξ : ℂ)) (𝓝 (b + e.phase (e.visit i ω) ω)) ∧
        Tendsto (e.referenceMean i ω) (𝓝[H] (η : ℂ)) (𝓝 b) ∧
        Tendsto (fun z => e.referenceMean i ω (φ z) - e.currentMean i ω z - chiC target.kappa * (L z).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 0))
    (hVisits : let target := j.target i d; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < e.visit i ω ∧ (e.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ e.event i)
    : ∃ (n : Ω → ℤ) (a : ℝ), Measurable[(j.target i d).walls] n ∧
      ∀ q : ℝ≥0, (j.target i d).Limit n a q := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  have hκ : 4 < 16 / (16 / i.kappa) := by rw [hdual]; exact i.kappa_gt_four
  refine ⟨fun _ => 0, e.offset, measurable_const, ?_⟩
  intro q
  rcases j with ⟨seed, outer, event, chart, infinite, twoLeft⟩
  cases twoLeft
  · have hs := pocketStopSideLimit_of_reference_germs_probes
      (P := d.measure) (ρL := wordL1 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight))
      (ρR := wordR2 (16 / i.kappa) (rs136Theta2 (16 / i.kappa) i.rightWeight))
      (xL := marksL1All) (xR := marksRAll (d.leftWall seed) (StripSys.rt seed) chart)
      (K := fun s => activeCompl event
        (if infinite then travAllInf d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart
          else travAll d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart)
        (pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart) s)
      (c := pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart)
      (a := e.offset) (δ := e.phase)
      hκ hDriven (fun ω _ => by rfl) (fun ω _ => by rfl) hZero hpre hOpen hFo
      hRawReference hLattice
      hCollar
      hProbes hJointGerms hVisits
    convert hs q using 1 <;>
      simp [SideTarget.Limit, SideTest.target, SideTarget.baseChart, PocketStopField.shiftChart]
  · have hs := pocketStopSideLimit_of_reference_germs_probes
      (P := d.measure) (ρL := wordL2 (16 / i.kappa) (rs136Theta1 (16 / i.kappa) i.leftWeight))
      (ρR := wordR2 (16 / i.kappa) (rs136Theta2 (16 / i.kappa) i.rightWeight))
      (xL := marksL2All d.rightWall chart)
      (xR := marksRAll (d.leftWall seed) (StripSys.rt seed) chart)
      (K := fun s => activeCompl event
        (if infinite then travAllInf d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart
          else travAll d.rightWall (d.leftWall seed) (StripSys.rt seed) d.curve chart)
        (pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart) s)
      (c := pChart event (fun ω => cfPocket (d.rightWall ω) (d.leftWall seed ω) (StripSys.rt seed)) chart)
      (a := e.offset) (δ := e.phase)
      hκ hDriven (fun ω _ => by rfl) (fun ω _ => by rfl) hZero hpre hOpen hFo
      hRawReference hLattice
      hCollar
      hProbes hJointGerms hVisits
    convert hs q using 1 <;>
      simp [SideTarget.Limit, SideTest.target, SideTarget.baseChart, PocketStopField.shiftChart]

/-- Four native pocket shapes with reference means, local-set facts and phase discharges supplied
by the latest germ/probe collector. Only its actual source inputs remain. -/
theorem late_pocketSideInput {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (d : WordObjects Ω) [IsProbabilityMeasure d.measure]
    (side : SideTest Ω → Late.SideData Ω)
    (hC : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration d.driver
      d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ q ω, Continuous (d.leftWall q ω))
    (hSidepre : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤ mΩ)
    (hSideFo : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
    (hSideRawReference : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event target.curve target.domain (refs.sets i) target.zeroField refs.level)
    (hSideLattice : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa)
    (hSideCollar : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
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
    (hSideProbes : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧ refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t)
    (hSideJointGerms : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ i, ∀ᵐ ω ∂target.measure, ω ∈ target.event → ω ∈ refs.event i →
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
    (hSideVisits : ∀ j : SideTest Ω, j.Ready d → let target := j.target i d; let refs := side j; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i)
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
  intro q hq G hG hPG hconf hζG hcfg hcfgI
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
      exact late_sideLimits i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, false, false⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      letI : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfg ω (hAG hω).1 (hAG hω).2).isDrivenCurve (hJordan ω hω)).1
      exact late_sideLimits i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)
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
      exact late_sideLimits i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)
    · intro hShape
      let j : SideTest Ω := ⟨q, G, A, ψ, true, false⟩
      have hj : j.Ready d := ⟨hq, hG, hPG, hconf, hζG, hcfg, hcfgI, hA, hAG, hPA, hJordan, hPoint, hShape⟩
      letI : IsProbabilityMeasure (j.target i d).measure := by
        change IsProbabilityMeasure d.measure
        infer_instance
      have hDriven : ∀ ω ∈ A, IsDrivenCurve ((j.target i d).curve ω) := by
        intro ω hω
        exact ((hcfgI ω (hAG hω).1 (le_antisymm (not_lt.1 (hAG hω).2) ((hconf ω (hAG hω).1).1.changeCorner_props.1.1))).isDrivenCurve (hJordan ω hω)).1
      exact late_sideLimits i d j (side j) hDriven (SideTest.isOpen_domain (i := i) hj)
        (isZeroBoundaryGFF_centredField hC hu₀')
        (hSidepre j hj) (hSideFo j hj) (hSideRawReference j hj) (hSideLattice j hj)
        (hSideCollar j hj) (hSideProbes j hj) (hSideJointGerms j hj) (hSideVisits j hj)

end InteractingSLE.Wire
