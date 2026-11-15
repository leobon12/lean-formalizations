/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideAncWire

/-!
# Theorems 1.2 and 1.3 without the late side anchor and without the late phase probes

PROVE-SIDE-ANCHOR. `late_sidePhaseZero` proves that on every Ready late side test the side phase vanishes at every
positive time, almost surely on the live event (Aux. lemma 122 in the bounded sector). Hence the late side data can be
replaced by **zeroed** data (`Late.SideData.zeroed`): the phase is `0` at positive times (and unchanged at time
`0`, where the exposed interval is empty), the mean probes are the constants `0, 0, 1`, and the candidate visits and
means are the canonical ones of `Late.SideData.anchored`. For the zeroed data

* the lattice binder holds (`late_zeroed_lattice`, from the original one at time `0`);
* the collar binder follows from the original one and `late_sidePhaseZero` (`late_zeroed_collar`);
* the probe binder holds deterministically (`late_zeroed_probes`);
* the joint-germ and visit binders hold (`Late.anchored_jointGerms`, `late_zeroed_visits`);

and all other side binders are the original ones. So `theorem12Statement_rise` / `theorem13Statement_rise` apply to the
zeroed data, and the wiring needs neither `hSideAnchor` nor `hSideProbes`:

* **`theorem12Statement_sideZero`**, **`theorem13Statement_sideZero`**: the binders of `theorem12Statement_sideLow` /
  `theorem13Statement_sideLow` except `hSideProbes`; conclusions unchanged.

Ruling R48/R74 as in `SideAncWire`.
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


namespace Late

/-- **The zeroed late side data**: phase `0` at positive times (unchanged at time `0`), constant mean probes
`0, 0, 1`, and the canonical candidate visits and means of `SideData.anchored`. All other fields are those of `e`. -/
def SideData.zeroed {Ω : Type} (e : SideData Ω) : SideData Ω :=
  SideData.anchored
    { e with
      phase := fun q ω => if q = 0 then e.phase 0 ω else 0
      probe := fun _ _ _ => 0
      baseProbe := fun _ _ _ => 0
      weight := fun _ _ _ => 1 }

theorem SideData.zeroed_phase {Ω : Type} (e : SideData Ω) (q : ℝ≥0) (ω : Ω) :
    e.zeroed.phase q ω = if q = 0 then e.phase 0 ω else 0 := rfl

theorem SideData.zeroed_phase_of_pos {Ω : Type} (e : SideData Ω) {q : ℝ≥0} (hq : 0 < q) (ω : Ω) :
    e.zeroed.phase q ω = 0 := by
  simp only [zeroed_phase, hq.ne', ↓reduceIte]

theorem SideData.zeroed_phase_zero {Ω : Type} (e : SideData Ω) (ω : Ω) : e.zeroed.phase 0 ω = e.phase 0 ω := by
  simp only [zeroed_phase, ↓reduceIte]

end Late

variable
    (hSeedG : ∀ κ, ZhanGT4.A1G3Calc.A1DualCouplingG3SeedGStatement κ)
    (hSeed : ∀ κ, ZhanGT4.A1EightSeed.A1DualCouplingEightSeedMStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{u})
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget0 : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{0})
    (hQ0 : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hChartLocal0 : Rise.ReadyLocalOn (rise_positiveReady hSeedG hSeed))
    (hChartZero0 : Night.ZeroChartStatement.{0})
    (hLaws : Hsd.Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 (night_rectG3 (dawn_fieldG3 hSeedG)))
        (late_coreEight (night_rectEight hSeed))))
    (hMeans : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseSide.R7PhaseMeansRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuterGeom : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → OuterIn.R7OuterGeomRemaining.{0} k rL rR)
    (hOuterPhase : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → OuterIn.R7OuterPhaseSideRemaining.{0} k rL rR)

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
variable (hRefWord : ∀ index, let x := word index; ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)

section
include hSideLattice

/-- The lattice binder for the zeroed side data. -/
theorem late_zeroed_lattice : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; ∀ q : ℝ≥0, ∀ᵐ ω ∂target.measure, ω ∈ target.event → (q : ℝ≥0∞) < capLife
        (target.curve ω) →
      ∃ m : ℤ, refs.phase q ω = m * phaseStep target.kappa := by
  intro index
  dsimp only
  intro j hj q
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq | hq
  · subst hq
    filter_upwards [hSideLattice index j hj 0] with ω hω hωA hl
    obtain ⟨m, hm⟩ := hω hωA hl
    exact ⟨m, by rw [Late.SideData.zeroed_phase_zero]; exact hm⟩
  · exact Eventually.of_forall fun ω _ _ => ⟨0, by rw [Late.SideData.zeroed_phase_of_pos _ hq]; simp⟩
end

section
include hSeedG hSeed hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl hWordu₀ hWordvα
  hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar

/-- The collar binder for the zeroed side data, from the original one and `late_sidePhaseZero`. -/
theorem late_zeroed_collar : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; let zL := Late.leftZero i d j; let zR := Late.rightZero i d j;
        ∀ q : ℝ≥0, ∀
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
                    zR q ω - segDriver (target.curve ω) q)).indicator 1 ξ - refs.offset := by
  intro index
  dsimp only
  intro j hj q gB hgB g hg
  have hcol := hSideCollar index j hj q gB hgB g hg
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq | hq
  · subst hq
    filter_upwards [hcol] with ω hω hωA hl v hv hvr ξ hξ
    obtain ⟨i', b, d', h1, h2, h3, h4⟩ := hω hωA hl v hv hvr ξ hξ
    exact ⟨i', b, d', h1, h2, h3, by rw [Late.SideData.zeroed_phase_zero]; exact h4⟩
  · have hz := late_sidePhaseZero hSeedG hSeed Ωw word wordSide hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr
      hWordl hWordu₀ hWordvα hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice
      hSideCollar index j hj q hq
    filter_upwards [hcol, hz] with ω hω hz' hωA hl v hv hvr ξ hξ
    obtain ⟨i', b, d', h1, h2, h3, h4⟩ := hω hωA hl v hv hvr ξ hξ
    refine ⟨i', b, d', h1, h2, h3, ?_⟩
    rw [Late.SideData.zeroed_phase_of_pos _ hq]
    rw [hz' hωA hl] at h4
    exact h4
end

/-- The probe binder for the zeroed side data (constant probes). -/
theorem late_zeroed_probes : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧ ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧
          refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t := by
  intro index
  dsimp only
  intro j hj N
  refine Eventually.of_forall fun ω _ => ⟨continuousOn_const, continuousOn_const, continuousOn_const,
    fun t ht => ⟨one_pos, ?_⟩⟩
  show (0 : ℝ) - 0 = (wordSide index j).zeroed.phase t ω * 1
  rw [Late.SideData.zeroed_phase_of_pos _ ht.1]
  ring

/-- The visit binder for the zeroed side data (a positive rational live time). -/
theorem late_zeroed_visits : ∀ index, let i := index; let x := word index;
    let d := Now.wordObjects i x (hWordS index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := (wordSide index j).zeroed; ∀ᵐ ω ∂target.measure, ω ∈ target.event → 0 < capLife (target.curve ω) →
      ∃ i, 0 < refs.visit i ω ∧ (refs.visit i ω : ℝ≥0∞) < capLife (target.curve ω) ∧ ω ∈ refs.event i := by
  intro index
  dsimp only
  intro j hj
  refine Eventually.of_forall fun ω _ hpos => ?_
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn hr0'
  have hq0' : 0 < ((q : ℝ)).toNNReal := Real.toNNReal_pos.2 hq0
  refine ⟨q, hq0', lt_trans (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe hq0.le).2 hqr)) hr, ?_⟩
  show (wordSide index j).zeroed.phase ((q : ℝ)).toNNReal ω = 0
  exact Late.SideData.zeroed_phase_of_pos _ hq0' ω

section
include hDy hRetarget hRefWord hWord𝔥 hSeedG hSeed hDy0 hRetarget0 hQ0 hChartLocal0 hChartZero0 hLaws hMeans
  hOuterGeom hOuterPhase hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl
  hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
  hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar

/-- **Theorem 1.2 without the late side anchor and the late phase probes**: `theorem12Statement_rise` applied to the
zeroed side data. -/
theorem theorem12Statement_sideZero : Exist.Theorem12Statement.{u} := by
  have hLat := late_zeroed_lattice Ωw word wordSide hWordS hSideLattice
  have hCol := late_zeroed_collar hSeedG hSeed Ωw word wordSide hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr
    hWordl hWordu₀ hWordvα hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar
  have hPr := late_zeroed_probes Ωw word wordSide hWordS
  have hVis := late_zeroed_visits Ωw word wordSide hWordS
  apply theorem12Statement_rise (Ωw := Ωw) (word := word) (wordSide := fun index j => (wordSide index j).zeroed)
    (hSideJointGerms := fun index j _ => Late.anchored_jointGerms _ _ _ _) <;> assumption
end

section
include hWord𝔥 hSeedG hSeed hDy0 hRetarget0 hQ0 hChartLocal0 hChartZero0 hLaws hMeans hOuterGeom hOuterPhase
  hWordBorel hWordProbability hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr hWordl
  hWorde hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
  hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar

/-- **Theorem 1.3 without the late side anchor and the late phase probes** (as `theorem12Statement_sideZero`). -/
theorem theorem13Statement_sideZero : Exist.Theorem13Statement.{u} := by
  have hLat := late_zeroed_lattice Ωw word wordSide hWordS hSideLattice
  have hCol := late_zeroed_collar hSeedG hSeed Ωw word wordSide hWordS hWordleft hWordright hWordθ₁ hWordθ₂ hWordr
    hWordl hWordu₀ hWordvα hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hSideLattice hSideCollar
  have hPr := late_zeroed_probes Ωw word wordSide hWordS
  have hVis := late_zeroed_visits Ωw word wordSide hWordS
  apply theorem13Statement_rise (Ωw := Ωw) (word := word) (wordSide := fun index j => (wordSide index j).zeroed)
    (hSideJointGerms := fun index j _ => Late.anchored_jointGerms _ _ _ _) <;> assumption
end

end InteractingSLE.Wire
