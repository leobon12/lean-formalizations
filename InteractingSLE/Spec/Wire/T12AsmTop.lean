/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12AsmInputs
import InteractingSLE.Spec.Wire.T12AsmSide
import InteractingSLE.Spec.Sec7.SideLCLattice

/-! # Theorems 1.2 and 1.3 assembled from committed providers

The remaining mathematical leaves are explicit: three A.1 C-law directions,
Prop. 5.1's dyadic fibre cover, later-root and node transfer, the raw chart,
R.5 up to phase, outer continuity and R.6 certificates, and raw side reference
and collar comparison. Physical word and version data remain explicit.
No full Theorem 1.2/1.3 or parametrized variant is used as an input.
-/
set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm

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


/-- The source side phase represented by its integer index. -/
def integerSide {Ω : Type} (i : BothLow) (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) : SideTest Ω → Late.SideData Ω :=
  fun j => (side j).intPhase (16 / (16 / i.kappa)) (idx j)

variable
    (hG3S : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ)
    (hG3F : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ)
    (hEightS : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hChartRaw : Relay.RawChartMembersOn.{0})
    (hRootLater : Night.RootLaterOn (cond44 hG3S hG3F hEightS)
      (Sec5.CrossCond.StagedNode.nodeObjects (cond44 hG3S hG3F hEightS)))
    (hNodeTransfer : Sec5.CrossCond.StagedNComp.NodeTransferStatement (cond44 hG3S hG3F hEightS))
    (hWordPhase : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      PhaseCont.R7PhaseWordRemaining.{0} k rL rR (π * chiC (16 / k)) 0)
    (hOuterCont : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterPhNext.R7OuterPhaseContRemaining.{0} k rL rR)
    (hR6Cert : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ¬ (rL < k - 6 ∧ rR < k - 6) → R6Rel.R6NestCertRemaining.{0} k rL rR)

variable (Ωw : BothLow → Type) [mWord : ∀ i, MeasurableSpace (Ωw i)]
    [hWordBorel : ∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [hWordProbability : ∀ i, IsProbabilityMeasure (baseWord i).measure]
    (wordSideZ : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i))
    (wordIdx : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → ℤ)
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hWordGFF : ∀ i, IsGFFWithBoundaryData (baseWord i).measure (baseWord i).field
      (baseWord i).boundary (baseWord i).jumps)
    (hWordCF : ∀ i, IsCenteredCounterflowDriver (16 / i.kappa) (baseWord i).measure (baseWord i).field
      (baseWord i).driver (baseWord i).lifetime)
    (hWordLife : ∀ i, ∀ᵐ ω ∂(baseWord i).measure, (baseWord i).lifetime ω = ⊤)

variable (hWordleft : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ a ∈
  Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
variable (hWordright : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ a ∈
  Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
variable (hWordθ₁ : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; x.thetaR
  ∈ Ioo (-(π / 2)) (π / 2))
variable (hWordθ₂ : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; x.thetaL
  ∈ Ioc (-(π / 2)) (π / 2))
variable (hWordu₀ : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i;
  IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
variable (hWordvα : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i;
  IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1
      x.rightWall)
variable (hWordvL : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ q,
  IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt
      (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
variable (hWordβc : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ ω,
  Continuous (x.outerWall ω))
variable (hWordβ0 : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ ω,
  x.outerWall ω 0 = 0)
variable (hWordβm : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ t,
  Measurable fun ω => x.outerWall ω t)
variable (hWordβtr : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ᵐ ω
  ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec
      0 ω).1 ⊤ (x.outerWall ω))
variable (hWordηc : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ ω,
  ContinuousOn (x.curve ω) (Ici 0))
variable (hWordηH : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ ω, ∀ t
  : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
variable (hWordη0 : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ ω,
  x.curve ω 0 = 0)
variable (hWordηm : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ t : ℝ,
  0 ≤ t → Measurable fun ω => x.curve ω t)
variable (hWordηtr : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ᵐ ω
  ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0
      => x.curve ω t))
variable (hWordu : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i;
  InnerProductSpace.HarmonicOnNhd x.harmonic H)
variable (hWordub : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∃ M : ℝ,
  ∀ z ∈ H, |x.harmonic z| ≤ M)
variable (hWord𝔥 : ∀ i, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) i; ∀ φ :
  TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
variable (hSidepre : ∀ index,
    let i := index
    let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord
      hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (cond44 hG3S hG3F hEightS) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := integerSide index (wordSideZ index) (wordIdx index) j;
        ∀ i, locPrefixSigma (refs.info i) target.event target.curve refs.level ≤
        (mWord index))
variable (hSideFo : ∀ index,
    let i := index
    let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord
      hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (cond44 hG3S hG3F hEightS) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := integerSide index (wordSideZ index) (wordIdx index) j;
        ∀ i ω, ω ∈ target.event → IsOpen (H \ refs.sets i ω))
variable (hSideRawReference : ∀ index,
    let i := index
    let x := (Relay.words (cond44 hG3S hG3F hEightS)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (cond44 hG3S hG3F hEightS) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := integerSide index (wordSideZ index) (wordIdx index) j;
        ∀ i, PocketStopUnionLaw (refs.info i) target.measure target.event
        target.curve target.domain (refs.sets i) target.zeroField refs.level)
variable (hSideCollar : ∀ index,
    let i := index
    let x := (Relay.words (cond44 hG3S hG3F hEightS)
      baseWord hWordb) index;
    let d := wordSafeObjects i x ((Relay.wordT (cond44 hG3S hG3F hEightS) baseWord hWordb hWordGFF
      hWordCF hWordLife hWordleft hWordright) index); ∀ j : SideTest (Ωw index), j.Ready d → let target := j.target i d;
        let refs := integerSide index (wordSideZ index) (wordIdx index) j;
        let zL := Late.leftZero i d j; let zR := Late.rightZero i d j; ∀ q : ℝ≥0, ∀
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
variable (hRefWord : ∀ index, let x := (Relay.words (cond44 hG3S hG3F hEightS) baseWord hWordb) index;
  ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)
section
include hG3S hG3F hEightS hDy0 hChartRaw hRootLater hNodeTransfer hWordPhase hOuterCont hR6Cert
  hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife hWordleft hWordright hWordθ₁ hWordθ₂
  hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
  hWordu hWordub hWord𝔥 hSidepre hSideFo hSideRawReference hSideCollar
include hDy hRefWord

/-- Theorem 1.2 with exactly the remaining committed-frontier leaves and physical data. -/
theorem theorem12Statement_assembled : Exist.Theorem12Statement.{u} := by
  have hG3C := g3Law hG3S hG3F
  have hEightC := eightLaw hEightS
  have hG := fun κ => Beacon.coreG3_of_lawC (hG3C κ)
  have hE := fun κ => Beacon.coreEight_of_lawC (hEightC κ)
  have hA := late_partAInputs hG hE
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := cond44 hG3S hG3F hEightS
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h4110 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  obtain ⟨hQ0, hChart0⟩ := Relay.qAndChart_of_raw h44 h470 hA
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h4110) hChartRaw
  have hLaws : Hsd.Fig51CandLawsStatement h44 :=
    Night.fig51CandLaws_of_parts h44 hA (Sec5.CrossCond.StagedNode.nodeObjects h44)
      (Sec5.CrossCond.StagedNode.rootPathOn_nodeObjects h44 hA) hRootLater
      (Sec5.CrossCond.StagedNPath.nodeLawOn_nodeObjects_of_transfer h44 hA hNodeTransfer)
      (Sec5.CrossCond.StagedNode.nodeBaseOn_nodeObjects h44)
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws hWordPhase hOuterCont
    (sharedVisits hG hE hDy0 hR6Cert)
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let word := Relay.words h44 baseWord hWordb
  let side := fun i => integerSide i (wordSideZ i) (wordIdx i)
  have hLat := fun index => lateSideLattice_intPhase index
    (wordSafeObjects index (word index) (hWordT index)) (wordSideZ index) (wordIdx index)
  have hLatZero := zeroedLattice Ωw word side hWordT hLat
  have hCol := zeroedCollar h44 Ωw word side hWordT hWordleft hWordright hWordθ₁ hWordθ₂
    hWordu₀ hWordvα hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hLat hSideCollar
  have hPr := zeroedProbes Ωw word side hWordT
  have hVis := zeroedVisits Ωw word side hWordT
  have hA2 := late_fourForceCrosscutG3LifeStatement hG
  have hA20 := late_threeForceCrosscutEightStatement hE
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have h51 := Beacon.prop51 hA hDy
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  apply theorem12Statement_current hA2 hA20 h47
    (Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg h51) hR7
  · apply Beacon.pocketWordFamily
      (hG3C := hG3C) (hEightC := hEightC)
      (Ωw := Ωw) (baseWord := baseWord) (wordSide := fun i j => (side i j).zeroed)
      (hSideLattice := hLatZero) (hSideCollar := hCol) (hSideProbes := hPr)
      (hSideJointGerms := fun index j _ => Late.anchored_jointGerms _ _ _ _)
      (hSideVisits := hVis) <;> assumption
  · apply Beacon.determinationReferenceFamily
      (hG3C := hG3C) (hEightC := hEightC)
      (Ωw := Ωw) (baseWord := baseWord) (wordSide := fun i j => (side i j).zeroed)
      (hSideLattice := hLatZero) (hSideCollar := hCol) (hSideProbes := hPr)
      (hSideJointGerms := fun index j _ => Late.anchored_jointGerms _ _ _ _)
      (hSideVisits := hVis) <;> assumption
end

section
include hG3S hG3F hEightS hDy0 hChartRaw hRootLater hNodeTransfer hWordPhase hOuterCont hR6Cert
  hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife hWordleft hWordright hWordθ₁ hWordθ₂
  hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH hWordη0 hWordηm hWordηtr
  hWordu hWordub hWord𝔥 hSidepre hSideFo hSideRawReference hSideCollar

/-- Theorem 1.3; the fibre cover is needed only at universe zero. -/
theorem theorem13Statement_assembled : Exist.Theorem13Statement.{u} := by
  have hG3C := g3Law hG3S hG3F
  have hEightC := eightLaw hEightS
  have hG := fun κ => Beacon.coreG3_of_lawC (hG3C κ)
  have hE := fun κ => Beacon.coreEight_of_lawC (hEightC κ)
  have hA := late_partAInputs hG hE
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := cond44 hG3S hG3F hEightS
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h4110 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  obtain ⟨hQ0, hChart0⟩ := Relay.qAndChart_of_raw h44 h470 hA
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h4110) hChartRaw
  have hLaws : Hsd.Fig51CandLawsStatement h44 :=
    Night.fig51CandLaws_of_parts h44 hA (Sec5.CrossCond.StagedNode.nodeObjects h44)
      (Sec5.CrossCond.StagedNode.rootPathOn_nodeObjects h44 hA) hRootLater
      (Sec5.CrossCond.StagedNPath.nodeLawOn_nodeObjects_of_transfer h44 hA hNodeTransfer)
      (Sec5.CrossCond.StagedNode.nodeBaseOn_nodeObjects h44)
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws hWordPhase hOuterCont
    (sharedVisits hG hE hDy0 hR6Cert)
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let word := Relay.words h44 baseWord hWordb
  let side := fun i => integerSide i (wordSideZ i) (wordIdx i)
  have hLat := fun index => lateSideLattice_intPhase index
    (wordSafeObjects index (word index) (hWordT index)) (wordSideZ index) (wordIdx index)
  have hLatZero := zeroedLattice Ωw word side hWordT hLat
  have hCol := zeroedCollar h44 Ωw word side hWordT hWordleft hWordright hWordθ₁ hWordθ₂
    hWordu₀ hWordvα hWordvL hWordηm hWordu hWordub hSidepre hSideFo hSideRawReference hLat hSideCollar
  have hPr := zeroedProbes Ωw word side hWordT
  have hVis := zeroedVisits Ωw word side hWordT
  have hA2 := late_fourForceCrosscutG3LifeStatement hG
  have hA20 := late_threeForceCrosscutEightStatement hE
  have h51 := Beacon.prop51 hA hDy0
  apply theorem13Statement_current h470 h51 hR7
  · apply Beacon.pocketWordFamily
      (hG3C := hG3C) (hEightC := hEightC)
      (Ωw := Ωw) (baseWord := baseWord) (wordSide := fun i j => (side i j).zeroed)
      (hSideLattice := hLatZero) (hSideCollar := hCol) (hSideProbes := hPr)
      (hSideJointGerms := fun index j _ => Late.anchored_jointGerms _ _ _ _)
      (hSideVisits := hVis) <;> assumption
  · exact hA2
  · exact hA20
end

end InteractingSLE.Wire.T12Asm
