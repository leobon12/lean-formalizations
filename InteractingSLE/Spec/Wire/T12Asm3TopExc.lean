/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm3Top
import InteractingSLE.Spec.Wire.T12Asm3Exc
import InteractingSLE.Spec.Wire.T12Asm3ExcSide

/-! # Theorems 1.2 and 1.3 from the restricted late-side collar (explicit physical context)

PROVE-T12-ASSEMBLE3 (collar rewire). `theorem12Statement_assembled3_ctx` / `theorem13Statement_assembled3_ctx` with the
late-side collar asked only off finite exceptional physical sets `X` (`LateSideCollarExc`, the form PROVE-SIDE-COLLAR2's
`lateSideCollarExc_originalReferences_of_conjugateMean_walls` concludes for exactly these installed side data,
`installedSide_eq_collar2`). The body is `T12Asm.theorem12Statement_assembled`'s, with Aux. 122 from
`sidePhaseZeroExc`/`zeroedCollarExc` and both Beacon families from `late_pocketSideInput_offExc` /
`wordSafe_pocketWordEvolution_offExc` (Aux. 29 at the excluded prime ends). No full Theorem 1.2/1.3 is used (R48).
-/
set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Bornology Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm3

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
    (hWordSplit : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → max rL rR = k / 2 - 4 →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Wall.R7SplitWordRemaining.{0} k rL rR c c')
    (hOuterCover : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      ∀ c c' : ℝ, π * chiC (16 / k) ≤ c → 0 ≤ c' → R5Out.R7OuterRelativeCoverMRemaining.{0} k rL rR c c')
    (hR6Mixed : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ∀ c : ℝ, π * chiC (16 / k) ≤ c →
      R6Safe.R6FaceSMixedRemaining.{0} k rL rR c 0 ∧ R6Safe.R6FaceSMixedInfRemaining.{0} k rL rR c 0 ∧
        R6Safe.R6FaceSMixedInfInfRemaining.{0} k rL rR c 0)
    (hR6Two : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Safe.R6FaceQTwoRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Safe.R6FaceQTwoInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0 ∧
        R6Safe.R6FaceQTwoInfInfRemaining.{0} k rL rR (π * chiC (16 / k)) 0)

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
variable (hSideCollar : ∀ index, LateSideCollarExc index
    (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
      (Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright index))
    (T12Ctx.installedSide index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
      (Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright index)
      (wordSideZ index) (wordIdx index)) (X index))
variable (hRefWord : ∀ index, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) index;
  ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)

section
include hDy0 hWordSplit hOuterCover hR6Mixed hR6Two hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH
  hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 X hXfin hSideCollar
include hDy hRefWord

/-- **Theorem 1.2 re-assembled, explicit physical context, restricted collar**: `theorem12Statement_assembled3_ctx`
with `LateSideCollarExc` for the installed side data and finite exceptional sets `X`. -/
theorem theorem12Statement_assembled3_ctxExc : Exist.Theorem12Statement.{u} := by
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
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws (wordPhase_of_split hWordSplit)
    (outerCont_of_cover hOuterCover)
    (T12Asm.sharedVisits hG hE hDy0 (r6Cert_of_faces hWordSplit hOuterCover hDy0 hR6Mixed hR6Two))
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let word := Relay.words h44 baseWord hWordb
  let side := fun i => T12Ctx.installedSide i (word i) (hWordT i) (wordSideZ i) (wordIdx i)
  have hRef := fun index => T12Asm2.refSide_facts index (word index) h44 (hWordT index) (hWordleft index)
    (hWordright index) (hWordθ₁ index) (hWordθ₂ index) (hWordu₀ index) (hWordvα index) (hWordvL index)
    (T12Ctx.visitLifts index (wordSafeObjects index (word index) (hWordT index)) (wordSideZ index))
    SideTest.rationalOriginalTime
  have hpre := fun index j hj r => (hRef index j hj r).1
  have hFo := fun index j hj r => (hRef index j hj r).2.1
  have hRaw := fun index j hj r => (hRef index j hj r).2.2
  have hLat := fun index => T12Ctx.installedSide_lattice index (word index) (hWordT index) (wordSideZ index)
    (wordIdx index)
  have hLatZero := T12Asm.zeroedLattice Ωw word side hWordT hLat
  have hCol := zeroedCollarExc h44 Ωw word side hWordT hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα
    hWordvL hWordηm hWordu hWordub hpre hFo hRaw hLat X hXfin hSideCollar
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
    exact wordSafe_pocketWordEvolution_offExc i (word i) h44 haux h4110 h470 (wordSafe_switched hA hChart0)
      (hWordT i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i) (hWordu₀ i) (hWordvα i) (hWordvL i)
      (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i) (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i)
      (hWordηtr i) (hWordu i) (hWordub i) (hWord𝔥 i) (fun j => (side i j).zeroed) (hpre i) (hFo i) (hRaw i)
      (hLatZero i) (X i) (hXfin i) (hCol i) (hPr i) (fun j _ => Late.anchored_jointGerms _ _ _ _) (hVis i)
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
    have hside := late_pocketSideInput_offExc i (wordSafeObjects i (word i) (hWordT i))
      (fun j => (side i j).zeroed)
      (by simpa only [wordSafeObjects, hdual] using hC) (by simpa only [wordSafeObjects, hdual] using hu')
      (hWordvα i).continuous (fun q => (hWordvL i q).continuous) (hpre i) (hFo i) (hRaw i) (hLatZero i)
      (hWordvα i).measurable (fun q => (hWordvL i q).measurable) (hWordηm i) (hWordu i) (hWordub i) (X i)
      (hXfin i) (hCol i) (hPr i) (fun j _ => Late.anchored_jointGerms _ _ _ _) (hVis i)
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
include hDy0 hWordSplit hOuterCover hR6Mixed hR6Two hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH
  hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 X hXfin hSideCollar

/-- **Theorem 1.3 re-assembled, explicit physical context, restricted collar** (as
`theorem12Statement_assembled3_ctxExc`). -/
theorem theorem13Statement_assembled3_ctxExc : Exist.Theorem13Statement.{u} := by
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
  have hR7 := Beacon.r7Reference hG hE hDy0 hQ0 hLaws (wordPhase_of_split hWordSplit)
    (outerCont_of_cover hOuterCover)
    (T12Asm.sharedVisits hG hE hDy0 (r6Cert_of_faces hWordSplit hOuterCover hDy0 hR6Mixed hR6Two))
  have hWordT := Relay.wordT h44 baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let word := Relay.words h44 baseWord hWordb
  let side := fun i => T12Ctx.installedSide i (word i) (hWordT i) (wordSideZ i) (wordIdx i)
  have hRef := fun index => T12Asm2.refSide_facts index (word index) h44 (hWordT index) (hWordleft index)
    (hWordright index) (hWordθ₁ index) (hWordθ₂ index) (hWordu₀ index) (hWordvα index) (hWordvL index)
    (T12Ctx.visitLifts index (wordSafeObjects index (word index) (hWordT index)) (wordSideZ index))
    SideTest.rationalOriginalTime
  have hpre := fun index j hj r => (hRef index j hj r).1
  have hFo := fun index j hj r => (hRef index j hj r).2.1
  have hRaw := fun index j hj r => (hRef index j hj r).2.2
  have hLat := fun index => T12Ctx.installedSide_lattice index (word index) (hWordT index) (wordSideZ index)
    (wordIdx index)
  have hLatZero := T12Asm.zeroedLattice Ωw word side hWordT hLat
  have hCol := zeroedCollarExc h44 Ωw word side hWordT hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα
    hWordvL hWordηm hWordu hWordub hpre hFo hRaw hLat X hXfin hSideCollar
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
    exact wordSafe_pocketWordEvolution_offExc i (word i) h44 haux h4110 h470 (wordSafe_switched hA hChart0)
      (hWordT i) (hWordleft i) (hWordright i) (hWordθ₁ i) (hWordθ₂ i) (hWordu₀ i) (hWordvα i) (hWordvL i)
      (hWordβc i) (hWordβ0 i) (hWordβm i) (hWordβtr i) (hWordηc i) (hWordηH i) (hWordη0 i) (hWordηm i)
      (hWordηtr i) (hWordu i) (hWordub i) (hWord𝔥 i) (fun j => (side i j).zeroed) (hpre i) (hFo i) (hRaw i)
      (hLatZero i) (X i) (hXfin i) (hCol i) (hPr i) (fun j _ => Late.anchored_jointGerms _ _ _ _) (hVis i)
  have h51 := Beacon.prop51 hA hDy0
  apply theorem13Statement_current h470 h51 hR7
  · exact hPocket
  · exact hA2
  · exact hA20
end

end InteractingSLE.Wire.T12Asm3
