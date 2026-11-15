/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm3TopExc
import InteractingSLE.Spec.Wire.T12Asm5Exc
import InteractingSLE.Spec.Wire.T12Asm5ExcSide
import InteractingSLE.Spec.Sec7.SideC19Refs

/-! # Theorems 1.2 and 1.3 from the late-side collar in R100's relifted current chart

PROVE-T12-ASSEMBLE5. `T12Asm4.theorem12Statement_assembled4_core` / `theorem13Statement_assembled4_core` with the
late-side collar binder in ruling R100's normalization, the form PROVE-SIDE-COLLAR2 proved with no input
(`SideC18.sideCollarInputExcShift_holds`, test-first restatement `SideC19.sideCollarInputExcRelift_holds`): the side
data are `SideC18.installedSideShift` (installed original-time references with lifts relifted by a walls-measurable
integer `m j`), and the collar `SideC18.LateSideCollarExcShift` reads the current chart `shiftChart baseChart (m j)`.
Its consumers are ASSEMBLE3's with the shift carried through (`T12Asm5.zeroedCollarExcShift`,
`T12Asm5.wordSafe_pocketWordEvolution_offExcShift`, `T12Asm5.late_pocketSideInput_offExcShift`): the native side
limit `PocketWordPerQ.PocketSideLimitInput0` allows any walls-measurable chart shift. The new binders are `wordM` and
its walls-measurability `hWordM`; the bodies are ASSEMBLE4's otherwise (`T12Asm5Final` feeds them). No full Theorem
1.2/1.3 or parametrized variant is used (R48).
-/
set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm5

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
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
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

variable (hWordleft : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ a ∈
  Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
variable (hWordright : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ a ∈
  Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
variable (hWordθ₁ : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; x.thetaR
  ∈ Ioo (-(π / 2)) (π / 2))
variable (hWordθ₂ : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; x.thetaL
  ∈ Ioc (-(π / 2)) (π / 2))
variable (hWordu₀ : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i;
  IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
variable (hWordvα : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i;
  IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1
      x.rightWall)
variable (hWordvL : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ q,
  IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt
      (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
variable (hWordβc : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
  Continuous (x.outerWall ω))
variable (hWordβ0 : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
  x.outerWall ω 0 = 0)
variable (hWordβm : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ t,
  Measurable fun ω => x.outerWall ω t)
variable (hWordβtr : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ᵐ ω
  ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec
      0 ω).1 ⊤ (x.outerWall ω))
variable (hWordηc : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
  ContinuousOn (x.curve ω) (Ici 0))
variable (hWordηH : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω, ∀ t
  : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar)
variable (hWordη0 : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
  x.curve ω 0 = 0)
variable (hWordηm : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ t : ℝ,
  0 ≤ t → Measurable fun ω => x.curve ω t)
variable (hWordηtr : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ᵐ ω
  ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0
      => x.curve ω t))
variable (hWordu : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i;
  InnerProductSpace.HarmonicOnNhd x.harmonic H)
variable (hWordub : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∃ M : ℝ,
  ∀ z ∈ H, |x.harmonic z| ≤ M)
variable (hWord𝔥 : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ φ :
  TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z)
variable (X : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → Set ℂ) (hXfin : ∀ i j q ω, (X i j q ω).Finite)
variable (wordM : ∀ i, SideTest (Ωw i) → Ωw i → ℤ)
variable (hWordM : ∀ index, let d := (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
    (Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright index));
  ∀ j : SideTest (Ωw index), j.Ready d → Measurable[(j.target index d).walls] (wordM index j))
variable (hSideCollar : ∀ index, SideC18.LateSideCollarExcShift index
    (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
      (Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright index))
    (SideC18.installedSideShift index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
      (Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright index)
      (wordSideZ index) (wordIdx index) (wordM index)) (wordM index) (X index))
variable (hRefWord : ∀ index, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) index;
  ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)

section
include hDy0 hWordPhase hOuterCont hR6Cert hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH
  hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 X hXfin hWordM hSideCollar
include hDy hRefWord

/-- **Theorem 1.2, explicit physical context, relifted collar, `T12Asm`'s R.5/R.6 binders**:
`T12Asm4.theorem12Statement_assembled4_core` with the late-side collar in R100's relifted current chart
(`SideC18.LateSideCollarExcShift` for `SideC18.installedSideShift`, shift `wordM`). -/
theorem theorem12Statement_assembled5_core : Exist.Theorem12Statement.{u} := by
  have hG3C := T12Asm.g3Law T12Asm2.g3S T12Asm2.g3F
  have hEightC := T12Asm.eightLaw T12Asm2.eightS
  have hG := fun κ => Beacon.coreG3_of_lawC (hG3C κ)
  have hE := fun κ => Beacon.coreEight_of_lawC (hEightC κ)
  have hA := late_partAInputs hG hE
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := T12Asm2.cond44Holds
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h4110 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  obtain ⟨hQ0, hChart0⟩ := Relay.qAndChart_of_raw h44 h470 hA
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h4110) Sec5.ChartRaw.rawChartMembersOn
  have hLaws : Hsd.Fig51CandLawsStatement h44 :=
    Night.fig51CandLaws_of_parts h44 hA (Sec5.CrossCond.StagedNode.nodeObjects h44)
      (Sec5.CrossCond.StagedNode.rootPathOn_nodeObjects h44 hA) T12Asm2.rootLater
      (Sec5.CrossCond.StagedNPath.nodeLawOn_nodeObjects_of_transfer h44 hA T12Asm2.nodeTransfer)
      (Sec5.CrossCond.StagedNode.nodeBaseOn_nodeObjects h44)
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws hWordPhase hOuterCont
    (T12Asm.sharedVisits hG hE hDy0 hR6Cert)
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let word := Relay.words h44 baseWord hWordb
  let side := fun i => SideC18.installedSideShift i (word i) (hWordT i) (wordSideZ i) (wordIdx i) (wordM i)
  have hRef := fun index => T12Asm2.refSide_facts index (word index) h44 (hWordT index) (hWordleft index)
    (hWordright index) (hWordθ₁ index) (hWordθ₂ index) (hWordu₀ index) (hWordvα index) (hWordvL index)
    (T12Ctx.visitLifts index (wordSafeObjects index (word index) (hWordT index)) (wordSideZ index))
    SideTest.rationalOriginalTime
  have hpre := fun index j hj r => (hRef index j hj r).1
  have hFo := fun index j hj r => (hRef index j hj r).2.1
  have hRaw := fun index j hj r => (hRef index j hj r).2.2
  have hLat := fun index => SideC19.installedSideShift_lattice index (word index) (hWordT index) (wordSideZ index)
    (wordIdx index) (wordM index)
  have hLatZero := T12Asm.zeroedLattice Ωw word side hWordT hLat
  have hCol := zeroedCollarExcShift h44 Ωw word side hWordT hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀
    hWordvα hWordvL hWordηm hWordu hWordub hpre hFo hRaw hLat X hXfin wordM hWordM hSideCollar
  have hPr := T12Asm.zeroedProbes Ωw word side hWordT
  have hVis := T12Asm.zeroedVisits Ωw word side hWordT
  have hA2 := late_fourForceCrosscutG3LifeStatement hG
  have hA20 := late_threeForceCrosscutEightStatement hE
  have hPocket : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Lemma725Ref.PocketWordEvolution.{0} κ rL rR := by
    intro κ hκ rL rR hL hLd hR hRd
    let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
    have haux : Sec4.Aux7Statement.{0} i.kappa := by
      have hs : Sec4.Aux7Statement.{0} (16 / (16 / i.kappa)) :=
        Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA (hWordT i).kappa_pos (hWordT i).kappa_lt_four
      have heq : 16 / (16 / i.kappa) = i.kappa := by field_simp
      rw [← heq]
      exact @hs
    exact wordSafe_pocketWordEvolution_offExcShift i (word i) h44 haux h4110 h470
      (wordSafe_switched hA hChart0) (hWordT i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i) (hWordu₀ i)
      (hWordvα i) (hWordvL i)
      (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i) (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i)
      (hWordηtr i) (hWordu i) (hWordub i) (hWord𝔥 i) (fun j => (side i j).zeroed) (hpre i) (hFo i) (hRaw i)
      (hLatZero i) (X i) (hXfin i) (wordM i) (hWordM i) (hCol i) (hPr i)
      (fun j _ => Late.anchored_jointGerms _ _ _ _) (hVis i)
  have hDet : Aux50Hit.Lemma725DetReferenceStatement.{u} := by
    apply lemma725DetReferenceStatement_ulift.{0, u}
    apply Lemma725RefSafe.lemma725DetReferenceStatement_of_pocketChartField
    intro κ hκ rL rR hL hLd hR hRd
    let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
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
    have hside := late_pocketSideInput_offExcShift i (wordSafeObjects i (word i) (hWordT i))
      (fun j => (side i j).zeroed)
      (by simpa only [wordSafeObjects, hdual] using hC) (by simpa only [wordSafeObjects, hdual] using hu')
      (hWordvα i).continuous (fun q => (hWordvL i q).continuous) (hpre i) (hFo i) (hRaw i) (hLatZero i)
      (hWordvα i).measurable (fun q => (hWordvL i q).measurable) (hWordηm i) (hWordu i) (hWordub i) (X i)
      (hXfin i) (wordM i) (hWordM i) (hCol i) (hPr i) (fun j _ => Late.anchored_jointGerms _ _ _ _) (hVis i)
    exact wordSafe_pocketChartField i (word i) hG hE hQ0 haux h4110 (wordSafe_switched hA hChart0) (hWordT i)
      (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i) (hWordu₀ i) (hWordvα i) (hWordvL i) (hWordβc i)
      (hWordβ0 i) (hWordβm i) (hWordβtr i) (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i) (hWordηtr i)
      (hWordu i) (hWordub i) hside (aux130RefFrame i) (aux130RefFrame_bounds i) (hRefWord i) hLaws
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have h51 := Beacon.prop51 hA hDy
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  exact theorem12Statement_current hA2 hA20 h47
    (Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg h51) hR7 hPocket hDet
end

section
include hDy0 hWordPhase hOuterCont hR6Cert hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH
  hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 X hXfin hWordM hSideCollar

/-- **Theorem 1.3, explicit physical context, relifted collar, `T12Asm`'s R.5/R.6 binders** (as
`theorem12Statement_assembled5_core`). -/
theorem theorem13Statement_assembled5_core : Exist.Theorem13Statement.{u} := by
  have hG3C := T12Asm.g3Law T12Asm2.g3S T12Asm2.g3F
  have hEightC := T12Asm.eightLaw T12Asm2.eightS
  have hG := fun κ => Beacon.coreG3_of_lawC (hG3C κ)
  have hE := fun κ => Beacon.coreEight_of_lawC (hEightC κ)
  have hA := late_partAInputs hG hE
  have h44 : AdmCode.Theorem12ParamCond44Statement.{0} := T12Asm2.cond44Holds
  have h470 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h4110 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h470 hA
  obtain ⟨hQ0, hChart0⟩ := Relay.qAndChart_of_raw h44 h470 hA
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h4110) Sec5.ChartRaw.rawChartMembersOn
  have hLaws : Hsd.Fig51CandLawsStatement h44 :=
    Night.fig51CandLaws_of_parts h44 hA (Sec5.CrossCond.StagedNode.nodeObjects h44)
      (Sec5.CrossCond.StagedNode.rootPathOn_nodeObjects h44 hA) T12Asm2.rootLater
      (Sec5.CrossCond.StagedNPath.nodeLawOn_nodeObjects_of_transfer h44 hA T12Asm2.nodeTransfer)
      (Sec5.CrossCond.StagedNode.nodeBaseOn_nodeObjects h44)
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws hWordPhase hOuterCont
    (T12Asm.sharedVisits hG hE hDy0 hR6Cert)
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let word := Relay.words h44 baseWord hWordb
  let side := fun i => SideC18.installedSideShift i (word i) (hWordT i) (wordSideZ i) (wordIdx i) (wordM i)
  have hRef := fun index => T12Asm2.refSide_facts index (word index) h44 (hWordT index) (hWordleft index)
    (hWordright index) (hWordθ₁ index) (hWordθ₂ index) (hWordu₀ index) (hWordvα index) (hWordvL index)
    (T12Ctx.visitLifts index (wordSafeObjects index (word index) (hWordT index)) (wordSideZ index))
    SideTest.rationalOriginalTime
  have hpre := fun index j hj r => (hRef index j hj r).1
  have hFo := fun index j hj r => (hRef index j hj r).2.1
  have hRaw := fun index j hj r => (hRef index j hj r).2.2
  have hLat := fun index => SideC19.installedSideShift_lattice index (word index) (hWordT index) (wordSideZ index)
    (wordIdx index) (wordM index)
  have hLatZero := T12Asm.zeroedLattice Ωw word side hWordT hLat
  have hCol := zeroedCollarExcShift h44 Ωw word side hWordT hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀
    hWordvα hWordvL hWordηm hWordu hWordub hpre hFo hRaw hLat X hXfin wordM hWordM hSideCollar
  have hPr := T12Asm.zeroedProbes Ωw word side hWordT
  have hVis := T12Asm.zeroedVisits Ωw word side hWordT
  have hA2 := late_fourForceCrosscutG3LifeStatement hG
  have hA20 := late_threeForceCrosscutEightStatement hE
  have hPocket : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Lemma725Ref.PocketWordEvolution.{0} κ rL rR := by
    intro κ hκ rL rR hL hLd hR hRd
    let i : BothLow := ⟨κ, rL, rR, hκ, hL, hLd, hR, hRd⟩
    have haux : Sec4.Aux7Statement.{0} i.kappa := by
      have hs : Sec4.Aux7Statement.{0} (16 / (16 / i.kappa)) :=
        Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA (hWordT i).kappa_pos (hWordT i).kappa_lt_four
      have heq : 16 / (16 / i.kappa) = i.kappa := by field_simp
      rw [← heq]
      exact @hs
    exact wordSafe_pocketWordEvolution_offExcShift i (word i) h44 haux h4110 h470
      (wordSafe_switched hA hChart0) (hWordT i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i) (hWordu₀ i)
      (hWordvα i) (hWordvL i)
      (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i) (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i)
      (hWordηtr i) (hWordu i) (hWordub i) (hWord𝔥 i) (fun j => (side i j).zeroed) (hpre i) (hFo i) (hRaw i)
      (hLatZero i) (X i) (hXfin i) (wordM i) (hWordM i) (hCol i) (hPr i)
      (fun j _ => Late.anchored_jointGerms _ _ _ _) (hVis i)
  have h51 := Beacon.prop51 hA hDy0
  apply theorem13Statement_current h470 h51 hR7
  · exact hPocket
  · exact hA2
  · exact hA20
end

end InteractingSLE.Wire.T12Asm5
