/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm3TopExc
import InteractingSLE.Spec.Sec7.SideC13Collar

/-! # Theorems 1.2 and 1.3 re-assembled: the final binder list

PROVE-T12-ASSEMBLE3. The explicit-context tops `theorem12Statement_assembled3_ctx` / `theorem13Statement_assembled3_ctx`
with

* the physical word context obtained from `T12Ctx.exists_physical_context` (PROVE-T12-WORDCTX), recorded as
  `PhysCtx` (its conclusion, field by field);
* the fibre covers `hDy`/`hDy0` from `Aux61Asm2.dyCover_of_record_both` (PROVE-AUX61-ASSEMBLE2): its restart families,
  contact rules and record inputs `RecordInputs` are the binders;
* the R.7 late-side collar as one named input `SideCollarInputExc`: in every physical context, the collar off finite
  exceptional physical sets (`LateSideCollarExc`, Lemma R.5's form; Aux. 29 covers the excluded prime ends through the
  `Exc` twins `T12Asm3Exc`, `T12Asm3ExcSide`, `T12Asm3TopExc`) holds for the installed side data
  (`T12Ctx.installedSide`) of some pre-side data and integer phase. By ruling R90 the pre-side data carry the
  normalized offset (the initial pocket-flow frame's); any normalizing installer of the form "installed data with
  overwritten offset" is such an instance (`installedSide_withOffset`). The unrestricted `SideCollarInput` implies it
  (`sideCollarInputExc_of_sideCollarInput`).

Remaining binders: the record inputs of the fibre covers, R.5's split-cover and incident-component inputs, R.6's
face descriptions, and `SideCollarInputExc`. No full Theorem 1.2/1.3 or parametrized variant is used (R48).
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



/-- **The physical word context** of the Theorem 1.2–1.3 tops: exactly the conclusion of
`T12Ctx.exists_physical_context`, field by field (the `hWord*` and `hRefWord` binders of `T12AsmTop`, plus the
boundary data, the actual angles and the identification of the harmonic representative with the coupled mean). -/
structure PhysCtx (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] (baseWord : ∀ i, Now.StripObjects (Ωw i))
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps) : Prop where
  boundary_eq : ∀ i, (baseWord i).boundary = T12Ctx.boundary i
  jumps_eq : ∀ i, (baseWord i).jumps = T12Ctx.jumps
  hWordGFF : ∀ i, IsGFFWithBoundaryData (baseWord i).measure (baseWord i).field
    (baseWord i).boundary (baseWord i).jumps
  hWordCF : ∀ i, IsCenteredCounterflowDriver (16 / i.kappa) (baseWord i).measure (baseWord i).field
    (baseWord i).driver (baseWord i).lifetime
  hWordLife : ∀ i, ∀ᵐ ω ∂(baseWord i).measure, (baseWord i).lifetime ω = ⊤
  hWordleft : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ a ∈
    Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
        x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa)
  hWordright : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ a ∈
    Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
        sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa)
  hWordθ₁ : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; x.thetaR
    ∈ Ioo (-(π / 2)) (π / 2)
  hWordθ₂ : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; x.thetaL
    ∈ Ioc (-(π / 2)) (π / 2)
  hWordu₀ : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i;
    IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean
  hWordvα : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i;
    IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1
        x.rightWall
  hWordvL : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ q,
    IsWallVersion x.measure (x.experiment (StripSys.betaSpec (StripSys.rt
        (positiveSeed q)) x.thetaL))
        (StripSys.rt (positiveSeed q)) (x.leftWall q)
  hWordβc : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
    Continuous (x.outerWall ω)
  hWordβ0 : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
    x.outerWall ω 0 = 0
  hWordβm : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ t,
    Measurable fun ω => x.outerWall ω t
  hWordβtr : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ᵐ ω
    ∂x.measure, IsGeneratingTrace (x.experiment StripSys.leftExtremalSpec
        0 ω).1 ⊤ (x.outerWall ω)
  hWordηc : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
    ContinuousOn (x.curve ω) (Ici 0)
  hWordηH : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω, ∀ t
    : ℝ, 0 ≤ t → x.curve ω t ∈ Hbar
  hWordη0 : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ ω,
    x.curve ω 0 = 0
  hWordηm : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ t : ℝ,
    0 ≤ t → Measurable fun ω => x.curve ω t
  hWordηtr : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ᵐ ω
    ∂x.measure, IsGeneratingTrace (fun t => x.driver t ω) ⊤ (fun t : ℝ≥0
        => x.curve ω t)
  hWordu : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i;
    InnerProductSpace.HarmonicOnNhd x.harmonic H
  hWordub : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∃ M : ℝ,
    ∀ z ∈ H, |x.harmonic z| ≤ M
  hWord𝔥 : ∀ i, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) i; ∀ φ :
    TestOn upperHalfPlaneOpens, x.mean φ = ∫ z, x.harmonic z * φ z
  hRefWord : ∀ index, let x := (Relay.words T12Asm2.cond44Holds baseWord hWordb) index;
    ∀ y ∉ counterflowJumps x.jumps ∪ Prop513Field.jumps (Real.exp (π *
        (aux130RefFrame index).x₀)) (stripHJumps {0} {(aux130RefFrame index).x₀}), counterflowData (16 / index.kappa)
        x.boundary y = stripCounterflowData (16 / index.kappa) 0 (Real.exp (π * (aux130RefFrame index).x₀)) (fig51Lower
        (aux130RefFrame index).a (aux130RefFrame index).b) (fig51Upper (aux130RefFrame index).x₀ (aux130RefFrame
        index).a' (aux130RefFrame index).b') y
  thetaR_eq : ∀ i, (Relay.words T12Asm2.cond44Holds baseWord hWordb i).thetaR =
    rs136Theta1 (16 / i.kappa) i.leftWeight
  thetaL_eq : ∀ i, (Relay.words T12Asm2.cond44Holds baseWord hWordb i).thetaL =
    rs136Theta2 (16 / i.kappa) i.rightWeight
  harmonic_eq : ∀ i, let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i;
    ∀ hc : IsCenteredCounterflowDriver (16 / i.kappa) x.measure x.field x.driver x.lifetime,
      x.harmonic = (counterflowObjects hc).mean

/-- The physical context's two-angle strip systems (`Relay.wordT`). -/
theorem PhysCtx.wordT {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}
    (hC : PhysCtx Ωw baseWord hWordb) :
    ∀ i, let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i;
      Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure x.field x.driver x.lifetime
        x.experiment :=
  Relay.wordT T12Asm2.cond44Holds baseWord hWordb hC.hWordGFF hC.hWordCF hC.hWordLife hC.hWordleft hC.hWordright

/-- **A physical word context exists** (`T12Ctx.exists_physical_context`). -/
theorem exists_physCtx : ∃ (Ωw : BothLow → Type) (mWord : ∀ i, MeasurableSpace (Ωw i))
    (_ : ∀ i, StandardBorelSpace (Ωw i)) (baseWord : ∀ i, @Now.StripObjects (Ωw i) (mWord i))
    (_ : ∀ i, IsProbabilityMeasure (baseWord i).measure)
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps),
    PhysCtx Ωw baseWord hWordb := by
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ := T12Ctx.exists_physical_context
  exact ⟨Ωw, mWord, hB, baseWord, hP, hWordb, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28⟩⟩

/-- **The R.7 late-side collar** (Lemma R.5's comparison at the late side tests), the remaining named input on the
side data: in every physical word context there are pre-side data and an integer phase whose installed side data
(`T12Ctx.installedSide`: visit-chart lifts, original-time reference hulls/records, integer phase, the pre-side
offset) satisfy `LateSideCollar`. Ruling R90: the pre-side offset is the initial pocket-flow frame's. -/
def SideCollarInput : Prop :=
  ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hC : PhysCtx Ωw baseWord hWordb),
    ∃ (wordSideZ : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i)) (wordIdx : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → ℤ),
      ∀ index, LateSideCollar index
        (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index))
        (T12Ctx.installedSide index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)
          (wordSideZ index) (wordIdx index))

/-- **The R.7 late-side collar off finite exceptional sets** (the remaining named input on the side data; the form
PROVE-SIDE-COLLAR2's `lateSideCollarExc_originalReferences_of_conjugateMean_walls` concludes): in every physical word
context there are pre-side data, an integer phase and finite exceptional physical sets `X` (Lemma R.5 gives no
comparison at the tip and the outgoing corner; Aux. 29 covers them) whose installed side data satisfy
`LateSideCollarExc`. Ruling R90: the pre-side offset is the initial pocket-flow frame's. -/
def SideCollarInputExc : Prop :=
  ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hC : PhysCtx Ωw baseWord hWordb),
    ∃ (wordSideZ : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i)) (wordIdx : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → ℤ)
      (X : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → Set ℂ), (∀ i j q ω, (X i j q ω).Finite) ∧
      ∀ index, LateSideCollarExc index
        (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index))
        (T12Ctx.installedSide index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)
          (wordSideZ index) (wordIdx index)) (X index)

/-- The unrestricted collar input gives the restricted one (`X = ∅`). -/
theorem sideCollarInputExc_of_sideCollarInput (h : SideCollarInput) : SideCollarInputExc := by
  intro Ωw _ _ baseWord _ hWordb hC
  obtain ⟨wordSideZ, wordIdx, hcol⟩ := h Ωw baseWord hWordb hC
  exact ⟨wordSideZ, wordIdx, fun _ _ _ _ => ∅, fun _ _ _ _ => Set.finite_empty,
    fun index => lateSideCollarExc_of_lateSideCollar _ _ _ _ (hcol index)⟩

/-- **PROVE-SIDE-COLLAR2's collar side data are the installed side data**: its
`lateSideCollarExc_originalReferences_of_conjugateMean_walls` concludes for
`((side j).withVisitLifts i j d (s j)).withOriginalReferences j d hKilled (s j)`; with `side` the integerized
pre-side data and `s := fun _ => SideTest.rationalOriginalTime` this is `T12Ctx.installedSide` (definitional). -/
theorem installedSide_eq_collar2 {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (i : BothLow)
    (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (hKilled : IsMeasurableKilledDriving (wordSafeObjects i x hS).driver (wordSafeObjects i x hS).forceL
      (wordSafeObjects i x hS).forceR (wordSafeObjects i x hS).lifetime) :
    T12Ctx.installedSide i x hS side idx = fun j =>
      (((side j).intPhase (16 / (16 / i.kappa)) (idx j)).withVisitLifts i j (wordSafeObjects i x hS)
        SideTest.rationalOriginalTime).withOriginalReferences j (wordSafeObjects i x hS) hKilled
        SideTest.rationalOriginalTime := rfl

/-- The restricted collar with no exceptional points is the unrestricted collar. -/
theorem lateSideCollar_of_exc_empty {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (h : LateSideCollarExc i d side fun _ _ _ => ∅) :
    LateSideCollar i d side := by
  intro j hj _ _ _ _ q gB hgB g hg
  filter_upwards [h j hj q gB hgB g hg] with ω hω hA hq v hv hvr ξ hξ
  exact hω hA hq v hv hvr ξ hξ (Set.notMem_empty _)

/-- **Theorem 1.2 re-assembled on the latest landed reductions** (PROVE-T12-ASSEMBLE3). Binders: the restart families,
contact rules and record inputs of Prop. 5.1's fibre covers at universes `u` and `0` (`dyCover_of_record_both`);
R.5 on the extremal pockets (`R5Wall.R7SplitWordRemaining`) and on the outer pockets
(`R5Out.R7OuterRelativeCoverMRemaining`, ruling R88), at margins `πχ(16/k) ≤ c`, `0 ≤ c'`; R.6's mixed and
two-outer-arm face descriptions; the late-side collar off finite exceptional sets `SideCollarInputExc`. The
physical word context is `T12Ctx.exists_physical_context`. -/
theorem theorem12Statement_assembled3
    (F : ∀ S : Sec5.Aux61SlitW.SourceSetting.{u}, Sec5.Aux61SlitW.SourceRestartData S.Ω S.nL S.nR)
    (Ta : ∀ S : Sec5.Aux61SlitW.SourceSetting.{u}, (F S).ι → Sec5.Aux61SlitW.SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI : ∀ S : Sec5.Aux61SlitW.SourceSetting.{u}, Sec5.Aux61Asm2.RecordInputs S (F S) (Ta S))
    (F₀ : ∀ S : Sec5.Aux61SlitW.SourceSetting.{0}, Sec5.Aux61SlitW.SourceRestartData S.Ω S.nL S.nR)
    (Ta₀ : ∀ S : Sec5.Aux61SlitW.SourceSetting.{0}, (F₀ S).ι → Sec5.Aux61SlitW.SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI₀ : ∀ S : Sec5.Aux61SlitW.SourceSetting.{0}, Sec5.Aux61Asm2.RecordInputs S (F₀ S) (Ta₀ S))
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
    (hSideCollar : SideCollarInputExc) :
    Exist.Theorem12Statement.{u} := by
  obtain ⟨hDy, hDy0⟩ := Sec5.Aux61Asm2.dyCover_of_record_both F Ta hI F₀ Ta₀ hI₀
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hC⟩ := exists_physCtx
  obtain ⟨wordSideZ, wordIdx, X, hXfin, hcol⟩ := hSideCollar Ωw baseWord hWordb hC
  exact @theorem12Statement_assembled3_ctxExc.{u} hDy hDy0 hWordSplit hOuterCover hR6Mixed hR6Two Ωw mWord hB
    baseWord hP wordSideZ wordIdx hWordb hC.hWordGFF hC.hWordCF
    hC.hWordLife hC.hWordleft hC.hWordright hC.hWordθ₁ hC.hWordθ₂ hC.hWordu₀ hC.hWordvα hC.hWordvL hC.hWordβc
    hC.hWordβ0 hC.hWordβm hC.hWordβtr hC.hWordηc hC.hWordηH hC.hWordη0 hC.hWordηm hC.hWordηtr hC.hWordu hC.hWordub
    hC.hWord𝔥 X hXfin hcol hC.hRefWord

/-- **Theorem 1.3 re-assembled on the latest landed reductions** (PROVE-T12-ASSEMBLE3): as
`theorem12Statement_assembled3`, with the fibre cover's record inputs only at universe `0`. -/
theorem theorem13Statement_assembled3
    (F₀ : ∀ S : Sec5.Aux61SlitW.SourceSetting.{0}, Sec5.Aux61SlitW.SourceRestartData S.Ω S.nL S.nR)
    (Ta₀ : ∀ S : Sec5.Aux61SlitW.SourceSetting.{0}, (F₀ S).ι → Sec5.Aux61SlitW.SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI₀ : ∀ S : Sec5.Aux61SlitW.SourceSetting.{0}, Sec5.Aux61Asm2.RecordInputs S (F₀ S) (Ta₀ S))
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
    (hSideCollar : SideCollarInputExc) :
    Exist.Theorem13Statement.{u} := by
  have hDy0 := Sec5.Aux61Asm2.dyCover_of_record F₀ Ta₀ hI₀
  obtain ⟨Ωw, mWord, hB, baseWord, hP, hWordb, hC⟩ := exists_physCtx
  obtain ⟨wordSideZ, wordIdx, X, hXfin, hcol⟩ := hSideCollar Ωw baseWord hWordb hC
  exact @theorem13Statement_assembled3_ctxExc.{u} hDy0 hWordSplit hOuterCover hR6Mixed hR6Two Ωw mWord hB baseWord
    hP wordSideZ wordIdx hWordb hC.hWordGFF hC.hWordCF
    hC.hWordLife hC.hWordleft hC.hWordright hC.hWordθ₁ hC.hWordθ₂ hC.hWordu₀ hC.hWordvα hC.hWordvL hC.hWordβc
    hC.hWordβ0 hC.hWordβm hC.hWordβtr hC.hWordηc hC.hWordηH hC.hWordη0 hC.hWordηm hC.hWordηtr hC.hWordu hC.hWordub
    hC.hWord𝔥 X hXfin hcol

end InteractingSLE.Wire.T12Asm3
