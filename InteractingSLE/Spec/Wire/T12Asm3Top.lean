/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm3Inputs
import InteractingSLE.Spec.Wire.T12Asm2Top
import InteractingSLE.Spec.Wire.T12CtxLifts
import InteractingSLE.Spec.Wire.T12CtxFamily
import InteractingSLE.Spec.Sec5.Aux61Asm2Path

/-! # Theorems 1.2 and 1.3 re-assembled on the latest landed reductions (explicit physical context)

PROVE-T12-ASSEMBLE3. `T12Asm.theorem12Statement_assembled` / `theorem13Statement_assembled` with every leaf that
landed work proves discharged (as in PROVE-T12-ASSEMBLE2: the A.1 laws, the raw chart, Prop. 5.9's later roots and
node transfer, the three raw-reference side leaves for the installed references), and the R.5/R.6 leaves from the
latest reductions (`T12Asm3Inputs`): PROVE-R5-WALL's split-cover word inputs, PROVE-R5-OUTER's incident-component
clauses (ruling R88) and PROVE-R6-SAFE's face descriptions.

The side data are PROVE-T12-WORDCTX's installed data `T12Ctx.installedSide`: the actual visit-chart lifts, the
original-time reference hulls/records (`T12Asm2.refSide`), the integer phase `wordIdx`, and the offset of the supplied
pre-side data `wordSideZ`. By ruling R90 the offset is normalized to the initial pocket-flow frame's; since the
installer keeps the pre-side offset (`T12Ctx.installedSide_fields`), R90's normalizing installer is the instance
`wordSideZ := ` (pre-side data with the normalized offset), see `installedSide_withOffset`.

`T12Asm3Final` closes the physical context with `T12Ctx.exists_physical_context`.
No full Theorem 1.2/1.3 or parametrized variant is used as an input (R48).
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


/-- R90's normalized installer as an instance of `T12Ctx.installedSide`: overwriting the offset of the installed side
data is installing the pre-side data with the overwritten offset (definitional). -/
theorem installedSide_withOffset {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (i : BothLow)
    (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (o : SideTest Ω → ℝ) :
    (fun j => { T12Ctx.installedSide i x hS side idx j with offset := o j }) =
      T12Ctx.installedSide i x hS (fun j => { side j with offset := o j }) idx := rfl

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
variable (hSideCollar : ∀ index, LateSideCollar index
    (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
      (Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright index))
    (T12Ctx.installedSide index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
      (Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright index)
      (wordSideZ index) (wordIdx index)))
variable (hRefWord : ∀ index, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) index;
  ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
      (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
      x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
      (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
      index).a' (aux130RefFrame index).b') y)

section
include hDy0 hWordSplit hOuterCover hR6Mixed hR6Two hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH
  hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 hSideCollar
include hDy hRefWord

/-- **Theorem 1.2 re-assembled, explicit physical context**: `T12Asm.theorem12Statement_assembled` with
PROVE-T12-ASSEMBLE2's discharges, R.5 from the split-cover and incident-component inputs, R.6 from the face
descriptions, and the side data installed by `T12Ctx.installedSide`. -/
theorem theorem12Statement_assembled3_ctx : Exist.Theorem12Statement.{u} := by
  have hT := Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let side := fun i => T12Ctx.visitLifts i
    (wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hT i)) (wordSideZ i)
  have hRef := fun index => T12Asm2.refSide_facts index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
    T12Asm2.cond44Holds (hT index) (hWordleft index) (hWordright index) (hWordθ₁ index) (hWordθ₂ index)
    (hWordu₀ index) (hWordvα index) (hWordvL index) (side index) SideTest.rationalOriginalTime
  exact T12Asm.theorem12Statement_assembled (hG3S := T12Asm2.g3S) (hG3F := T12Asm2.g3F)
    (hEightS := T12Asm2.eightS) (hDy := hDy) (hDy0 := hDy0) (hChartRaw := Sec5.ChartRaw.rawChartMembersOn)
    (hRootLater := T12Asm2.rootLater) (hNodeTransfer := T12Asm2.nodeTransfer)
    (hWordPhase := wordPhase_of_split hWordSplit) (hOuterCont := outerCont_of_cover hOuterCover)
    (hR6Cert := r6Cert_of_faces hWordSplit hOuterCover hDy0 hR6Mixed hR6Two) (Ωw := Ωw) (baseWord := baseWord)
    (wordSideZ := T12Asm2.refWordSide (Relay.words T12Asm2.cond44Holds baseWord hWordb) hT side)
    (wordIdx := wordIdx) (hWordb := hWordb) (hWordGFF := hWordGFF) (hWordCF := hWordCF)
    (hWordLife := hWordLife) (hWordleft := hWordleft) (hWordright := hWordright) (hWordθ₁ := hWordθ₁)
    (hWordθ₂ := hWordθ₂) (hWordu₀ := hWordu₀) (hWordvα := hWordvα) (hWordvL := hWordvL) (hWordβc := hWordβc)
    (hWordβ0 := hWordβ0) (hWordβm := hWordβm) (hWordβtr := hWordβtr) (hWordηc := hWordηc) (hWordηH := hWordηH)
    (hWordη0 := hWordη0) (hWordηm := hWordηm) (hWordηtr := hWordηtr) (hWordu := hWordu) (hWordub := hWordub)
    (hWord𝔥 := hWord𝔥)
    (hSidepre := fun index j hj r => (hRef index j hj r).1)
    (hSideFo := fun index j hj r => (hRef index j hj r).2.1)
    (hSideRawReference := fun index j hj r => (hRef index j hj r).2.2)
    (hSideCollar := hSideCollar) (hRefWord := hRefWord)
end

section
include hDy0 hWordSplit hOuterCover hR6Mixed hR6Two hWordBorel hWordProbability hWordb hWordGFF hWordCF hWordLife
  hWordleft hWordright hWordθ₁ hWordθ₂ hWordu₀ hWordvα hWordvL hWordβc hWordβ0 hWordβm hWordβtr hWordηc hWordηH
  hWordη0 hWordηm hWordηtr hWordu hWordub hWord𝔥 hSideCollar

/-- **Theorem 1.3 re-assembled, explicit physical context** (as `theorem12Statement_assembled3_ctx`; the fibre
cover only at universe zero, no reference-frame word equality). -/
theorem theorem13Statement_assembled3_ctx : Exist.Theorem13Statement.{u} := by
  have hT := Relay.wordT T12Asm2.cond44Holds baseWord hWordb hWordGFF hWordCF hWordLife hWordleft hWordright
  let side := fun i => T12Ctx.visitLifts i
    (wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hT i)) (wordSideZ i)
  have hRef := fun index => T12Asm2.refSide_facts index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
    T12Asm2.cond44Holds (hT index) (hWordleft index) (hWordright index) (hWordθ₁ index) (hWordθ₂ index)
    (hWordu₀ index) (hWordvα index) (hWordvL index) (side index) SideTest.rationalOriginalTime
  exact @T12Asm.theorem13Statement_assembled.{u} (hG3S := T12Asm2.g3S) (hG3F := T12Asm2.g3F)
    (hEightS := T12Asm2.eightS) (hDy0 := hDy0) (mWord := mWord) (hWordBorel := hWordBorel)
    (hWordProbability := hWordProbability) (hChartRaw := Sec5.ChartRaw.rawChartMembersOn)
    (hRootLater := T12Asm2.rootLater) (hNodeTransfer := T12Asm2.nodeTransfer)
    (hWordPhase := wordPhase_of_split hWordSplit) (hOuterCont := outerCont_of_cover hOuterCover)
    (hR6Cert := r6Cert_of_faces hWordSplit hOuterCover hDy0 hR6Mixed hR6Two) (Ωw := Ωw) (baseWord := baseWord)
    (wordSideZ := T12Asm2.refWordSide (Relay.words T12Asm2.cond44Holds baseWord hWordb) hT side)
    (wordIdx := wordIdx) (hWordb := hWordb) (hWordGFF := hWordGFF) (hWordCF := hWordCF)
    (hWordLife := hWordLife) (hWordleft := hWordleft) (hWordright := hWordright) (hWordθ₁ := hWordθ₁)
    (hWordθ₂ := hWordθ₂) (hWordu₀ := hWordu₀) (hWordvα := hWordvα) (hWordvL := hWordvL) (hWordβc := hWordβc)
    (hWordβ0 := hWordβ0) (hWordβm := hWordβm) (hWordβtr := hWordβtr) (hWordηc := hWordηc) (hWordηH := hWordηH)
    (hWordη0 := hWordη0) (hWordηm := hWordηm) (hWordηtr := hWordηtr) (hWordu := hWordu) (hWordub := hWordub)
    (hWord𝔥 := hWord𝔥)
    (hSidepre := fun index j hj r => (hRef index j hj r).1)
    (hSideFo := fun index j hj r => (hRef index j hj r).2.1)
    (hSideRawReference := fun index j hj r => (hRef index j hj r).2.2)
    (hSideCollar := hSideCollar)
end

end InteractingSLE.Wire.T12Asm3
