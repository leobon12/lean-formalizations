/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.WordSafeSystem
import InteractingSLE.Spec.Sec7.StripSafeGerm
import InteractingSLE.Spec.Sec5.RestartGenWalls
import InteractingSLE.Spec.Sec5.RestartGenConsumers
import InteractingSLE.Spec.Sec5.RestartGenReflect
import InteractingSLE.Spec.Sec7.Aux37GermFlowStrip
import InteractingSLE.Spec.Sec7.Aux37AssemblyStrip
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofWire
import InteractingSLE.Spec.Sec7.Aux37FrameAssembly
import InteractingSLE.Spec.Sec7.Aux37SideAssembly
import InteractingSLE.Spec.Sec7.Aux37SideInfFrame
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofHwit
import InteractingSLE.Spec.Sec7.StripMarks513
import InteractingSLE.Spec.Sec7.StripPocketPathFinal
import InteractingSLE.Spec.Sec7.StripPocketPathLate
import InteractingSLE.Spec.Sec7.StripPocketPathWalls

/-!
# Ports to the two-angle strip system, part 1

Packet PROVE-WORDSAFE. Copies of the pocket-word lemmas below with `StripSys.IsStripSystem` weakened to
`WordSafe.IsTwoAngleStripSystem` (same statements otherwise, same proofs; they read the strip system's
staged histories only at `constSpec θ` and `twoAngleSpec θ₀ t₀ θ`). Calls to ported lemmas are redirected to
the ports (`WordSafe.…`); calls to PROVE-STRIPSYS-SAFE's constant-angle ports go through
`IsTwoAngleStripSystem.toConst`. Each section names its source file. No new mathematics.

Ported: `firstPiece_isFlowLine`, `ae_eq_firstPiece_of_le`, `ae_isFirstHitQ_twoAngle_le`,
`SwitchedWallFirstHitStatement`, `ae_isFirstHitQ_twoAngle`, `hfirstL_of_restartGen`, `ae_isFirstHitQ_twoAngle_le_neg`,
`ae_isFirstHitQ_alpha`, `ae_ownHeights_union_strip`, `ae_noFrame_strip`, `strip_walls_inputs`,
`flatClockStatement_strip`, `exists_isLocalSetMean_strip`, `hwit_of_sideGerm`, `pocketSideGermStatement_of_traces`,
`ae_ownTrace_alpha`, `ae_ownTrace_beta`, `hwit_of_flatClock`, `hwitI_of_flatClock`, `flatClockStatement_strip_rat`,
`exists_isLocalSetMean_strip_rat`, `hwit_of_wallMeans`, `hwitI_of_wallMeans`, `stripCounterflow_isFlowLineDriver`,
`ae_transient_counterflow`, `exists_ae_leftExtremal_eq_admDrv`, `hdet_leftExtremal`,
`ae_simple_trace_leftExtremal_strip`, `ae_isSimpleProper_leftExtremal`, `ae_driver_betaSpec_eq_leftExtremal`,
`ae_eq_leftExtremal_of_le`, `ae_isFirstHitQ_leftExtremal`, `hfirstE_of_restartGen`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.WordSafe

section
-- from InteractingSLE/Spec/Sec5/RestartGenWalls.lean
open InteractingSLE.Sec5 InteractingSLE.Sec5.RestartGen
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open WangWu (negInv negInv_negInv')
open Prop411Q (IsFirstHitQ)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.StripSideHeightProb (catPath catPath_of_le)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The first piece of a two-angle wall as a flow line**: the seed line of the first piece's driver is a version
of the angle-`θ₀` flow line of `h` (frozen `IsFlowLine`), almost surely of infinite lifetime, with a continuous
driver from `0`. -/
theorem firstPiece_isFlowLine (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (t₀ : ℝ≥0) :
    IsFlowLine κ b J 0 θ₀ P h
      (fun ω t => WangWu.seedLine (fun ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).2)
        (fun t ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1 t) ω t)
      (fun ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).2) ∧
    ∀ᵐ ω ∂P, (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).2 = ⊤ ∧
      (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1 0 = 0 ∧ Continuous (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1 ∧
      IsGeneratingTrace (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1 ⊤
        (fun t => WangWu.seedLine (fun ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).2)
          (fun t ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1 t) ω t) := by
  set spec := Sec7.StripSys.twoAngleSpec θ₀ t₀ θ with hspec
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hst : IsStagedHistory κ b J P h spec (E spec) :=
    hS.stagedTwoAngle hθ₀ hθ t₀
  have hd := Sec7.StripWall.isFlowLineDriver_stage_zero hκ hb hS.gff hst
  have hθh := heights_of_cum hκ hκ4 hleft hright hθ₀
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  have hadm := Sec7.R7Outer.hasAdmissiblePartialSums_of_heights hκ hκ4 hb hθh
  have hgood : ∀ᵐ ω ∂P, (E spec 0 ω).2 = ⊤ ∧ (E spec 0 ω).1 0 = 0 ∧ Continuous (E spec 0 ω).1 ∧
      IsGeneratingTrace (E spec 0 ω).1 ⊤
        (fun t => WangWu.seedLine (fun ω => (E spec 0 ω).2) (fun t ω => (E spec 0 ω).1 t) ω t) := by
    obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := hd
    filter_upwards [Cond44Ref.ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1, hC.1.2.2.2.2]
      with ω ⟨hζ, ⟨η₀, hη₀, hsl⟩, _⟩ hpath
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    have hc : Continuous (E spec 0 ω).1 := by
      have := hcw
      simp only [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    refine ⟨hζ, hw0, hc, ?_⟩
    have e : (fun t : ℝ≥0 => WangWu.seedLine (fun ω => (E spec 0 ω).2) (fun t ω => (E spec 0 ω).1 t) ω t) = η₀ :=
      funext fun t => by rw [hsl]; simp only [Real.toNNReal_coe]
    rw [e]
    exact hη₀
  refine ⟨Sec7.StripWall.isFlowLine_of_isFlowLineDriver hd ?_, hgood⟩
  filter_upwards [hgood] with ω hω
  rw [hω.1]
  exact hω.2.2.2

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Before the switch a two-angle wall is its first piece**: almost surely a version of the wall agrees with the
seed line of the first piece on `[0, t₀]` (both generate the first piece's driver there). -/
theorem ae_eq_firstPiece_of_le (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {R : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ t₀ → R ω t = WangWu.seedLine (fun ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).2)
      (fun t ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1 t) ω t := by
  filter_upwards [(WordSafe.firstPiece_isFlowLine hS hleft hright hθ₀ hθ t₀).2, hR.ae_isGeneratingTrace]
    with ω ⟨_, hw0, hc, hγ⟩ hRω t ht
  have hR' := IsGeneratingTrace.of_eqOn_lt hRω (T := (t₀ : ℝ≥0∞))
    (w := (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1) fun s hs =>
      (catPath_of_le (ENNReal.coe_lt_coe.1 hs).le).symm
  exact IsGeneratingTrace.eq_of_le hR' (LP.isGeneratingTrace_mono hγ le_top) hc.continuousOn hw0
    (ENNReal.coe_le_coe.2 ht)

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The one-angle law before the switch of a two-angle wall** (`q ≤ t₀`): the wall is its first piece there, the
angle-`θ₀` flow line of `h`, and Lemma 4.7 at relative angle `θ₀` applies (`ae_isFirstHitQ_of_isFlowLine_heights`). -/
theorem ae_isFirstHitQ_twoAngle_le {θ₀ θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ₀)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {R : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q)
    (hqt : (q : ℝ) ≤ t₀) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hfl := (WordSafe.firstPiece_isFlowLine hS hleft hright hθ₀ hθ t₀).1
  have hπ := heights_of_cum hκ hκ4 hleft hright Sec7.StripSys.pi_div_two_mem_Icc
  filter_upwards [ae_isFirstHitQ_of_isFlowLine_heights h47 href hκ hκ4 hS.boundaryData
      (heights_of_cum hκ hκ4 hleft hright hθ₀) hπ hS.gff hS.counterflow hS.lifetime hη hfl q hq,
    WordSafe.ae_eq_firstPiece_of_le hS hleft hright hθ₀ hθ hR] with ω h1 h2
  refine isFirstHitQ_congr (by exact_mod_cast hq) (fun s hs => ?_) (fun u _ => rfl) h1
  simp only [Sec7.Lemma71I.realPath]
  exact (h2 _ ((Real.toNNReal_le_iff_le_coe).2 (hs.2.trans hqt))).symm

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The general restart law for the walls, after the switch** (named input; specification Lemma 5.7, p. 138, with
`ℓ = 2`, Figure 5.5 right panel, and Remark 5.8 (c); Aux. lemma 130, pp. 410–412). For every strip system with Aux.
130's height choice, every two-angle wall `η^{t₀,∞}_{θ₀,θ}` (angles in `[−π/2, π/2]`) with a version `R`, and every
continuous generating trace `η` of the counterflow driver: at every rational own time `q > t₀` after the switch,
almost surely the counterflow `R ∘ η` first contacts `R((0, q])` at `R(q)`. Mathematically: given the angle-varying
prefix `R([0, q])`, the counterflow mapped to the remaining domain is the counterflow of the conditional field, whose
data satisfy Lemma 4.5's heights, so it exits at the tip. Before the switch the law is proved
(`WordSafe.ae_isFirstHitQ_twoAngle_le`). -/
def SwitchedWallFirstHitStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), IsTwoAngleStripSystem κ b J P h W' ζ' E →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) →
    ∀ θ₀ θ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → θ ∈ Icc (-(π / 2)) (π / 2) →
    ∀ (t₀ : ℝ≥0) (R : Ω → ℝ≥0 → ℂ),
      Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∀ q : ℚ, (t₀ : ℝ) < q →
      ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The restart law at every rational time of a two-angle wall**: before the switch from Lemma 4.7 at relative
angle `θ₀`, after it from the general law. -/
theorem ae_isFirstHitQ_twoAngle {θ₀ θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ₀)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : WordSafe.SwitchedWallFirstHitStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {R : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  rcases le_or_gt (q : ℝ) t₀ with hqt | hqt
  · exact WordSafe.ae_isFirstHitQ_twoAngle_le h47 href hS hleft hright hθ₀ hθ hR hη q hq hqt
  · exact hsw κ b J P h W' ζ' E hS hleft hright θ₀ θ hθ₀ hθ t₀ R hR η hη q hqt

end

section
-- from InteractingSLE/Spec/Sec5/RestartGenConsumers.lean
open InteractingSLE.Sec5 InteractingSLE.Sec5.RestartGen
open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.StripSideHeightProb (catPath)
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hfirstL`** (the walls `β^{(r)} = η^{r,∞}_{π/2,θ₂}`): the landed Lemma 4.7 before the switch at own time `r`,
the general law after it. -/
theorem hfirstL_of_restartGen (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : WordSafe.SwitchedWallFirstHitStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2)) {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hvL : ∀ q, Sec7.StripWall.IsWallVersion P
      (E (Sec7.StripSys.betaSpec (Sec7.StripSys.rt (Sec7.PocketWordIn.positiveSeed q)) θ₂))
      (Sec7.StripSys.rt (Sec7.PocketWordIn.positiveSeed q)) (Lr q)) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ r : ℚ, 0 < r → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (Lr r ω)) (η ω) q := by
  intro r _ q hq
  filter_upwards [WordSafe.ae_isFirstHitQ_twoAngle (η := fun ω (t : ℝ≥0) => η ω t) (lemma47QHitTStatement_pi_div_two
      h47)
    href hsw hS hleft hright Sec7.StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθ₂) (hvL r) hηtr q hq]
    with ω hω
  exact isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω

end

section
-- from InteractingSLE/Spec/Sec5/RestartGenReflect.lean
open InteractingSLE.Sec5 InteractingSLE.Sec5.RestartGen
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps reflField mem_reflJumps)
open Sec7.StripSideHeightProb (catPath)
open Exist.Staged (IsRegularDriver)
open LP (reflectC reflectC_reflectC)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Before the switch of a wall with first angle `−π/2`**, from the landed Lemma 4.7 (by reflection). -/
theorem ae_isFirstHitQ_twoAngle_le_neg {θ : ℝ} (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0} {R : Ω → ℝ≥0 → ℂ}
    (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec (-(π / 2)) t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q)
    (hqt : (q : ℝ) ≤ t₀) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hfl := (WordSafe.firstPiece_isFlowLine hS hleft hright Sec7.StripSys.neg_pi_div_two_mem_Icc hθ t₀).1
  filter_upwards [ae_isFirstHitQ_of_isFlowLine_neg_pi_div_two h47 href hκ hκ4 hS.boundaryData
      (isHeightBounded44_reflData_of_cum hκ hκ4 hleft hright) hS.gff hS.counterflow hS.lifetime hη hfl q hq,
    WordSafe.ae_eq_firstPiece_of_le hS hleft hright Sec7.StripSys.neg_pi_div_two_mem_Icc hθ hR] with ω h1 h2
  refine isFirstHitQ_congr (by exact_mod_cast hq) (fun s hs => ?_) (fun u _ => rfl) h1
  simp only [Sec7.Lemma71I.realPath]
  exact (h2 _ ((Real.toNNReal_le_iff_le_coe).2 (hs.2.trans hqt))).symm

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The restart law at every rational time of a wall with first angle `−π/2`**: the landed Lemma 4.7 before the
switch, the general law after it. -/
theorem ae_isFirstHitQ_alpha {θ : ℝ} (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : WordSafe.SwitchedWallFirstHitStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0} {R : Ω → ℝ≥0 → ℂ}
    (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec (-(π / 2)) t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  rcases le_or_gt (q : ℝ) t₀ with hqt | hqt
  · exact WordSafe.ae_isFirstHitQ_twoAngle_le_neg h47 href hS hleft hright hθ hR hη q hq hqt
  · exact hsw κ b J P h W' ζ' E hS hleft hright (-(π / 2)) θ Sec7.StripSys.neg_pi_div_two_mem_Icc hθ t₀ R hR η hη q
      hqt

end

section
-- from InteractingSLE/Spec/Sec7/Aux37GermFlowStrip.lean
open InteractingSLE.Sec7.Aux37Germ
open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar logDerivFwd fwdMap chiC)
open PocketCoord PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux119Heights StripWall
  StripSideHeightProb
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**(G1) for the strip system** (see the module docstring): the walls `β = β^{(r)}`, `α` of the strip system with
Aux. lemma 130's heights, versions of their traces, their entrance-history locality, any hitting-measurable local set
`A` (e.g. the counterflow hull at a fixed time, `isLocalSet_cfHull`), and versions of the means. -/
theorem ae_ownHeights_union_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    {A : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A) (hAloc : IsLocalSet A (WholeField.centredField h u₀) P)
    {g gU : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ wallUnion β α ω) (WholeField.centredField h u₀) P g)
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => β ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gL q))
    (hgR : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 q ∩ H) (WholeField.centredField h u₀) P (gR q)) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ (A ω ∪ wallUnion β α ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ wallUnion β α ω) → g ω φ = ∫ z, v z * φ z) →
      ∀ (r' : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (α ω) (β ω) r' Ψ c →
      changePocket (α ω) (β ω) r' ⊆ leftSideOf (range (α ω)) →
      (∀ s : ℝ≥0, β ω s ∉ range (α ω) → s ≠ r → (∃ ε > 0, A ω ∩ ball (β ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ =>
            catPath (E (StripSys.betaSpec r θ₂) 0 ω).1 r (E (StripSys.betaSpec r θ₂) 1 ω).1 t.toNNReal) q z).im)
          (𝓝[changePocket (α ω) (β ω) r'] (β ω s))
          (𝓝 (sleLambda κ - (if s < r then π / 2 else θ₂) * chiC κ))) ∧
      (∀ s : ℝ≥0, α ω s ∉ range (β ω) → s ≠ 1 → (∃ ε > 0, A ω ∩ ball (α ω s) ε = ∅) → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z + u₀ z + chiC κ * (logDerivFwd (fun t : ℝ =>
            catPath (E (StripSys.alphaSpec θ₁) 0 ω).1 1 (E (StripSys.alphaSpec θ₁) 1 ω).1 t.toNNReal) q z).im)
          (𝓝[changePocket (α ω) (β ω) r'] (α ω s))
          (𝓝 (-sleLambda κ - (if s < 1 then -(π / 2) else θ₁) * chiC κ))) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec (-(π / 2)) 1 θ₁) (E (StripSys.alphaSpec θ₁)) :=
    hS.isStagedHistory_alpha hθ₁
  have hEβ : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec (π / 2) r θ₂) (E (StripSys.betaSpec r θ₂)) :=
    hS.isStagedHistory_beta hθ₂ r
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁) (hcumR _ hθ₁)
      hθ₁.1 (by linarith [hθ₁.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂)
      (fun y hy hyJ => by have := hcumR _ hθ₂ y hy hyJ; linarith) hθ₂.2 (by linarith [hθ₂.1])
  exact ae_ownHeights_union_twoAngle hκ hκ4 hb hh hu₀ hEβ hregβ (hL44 _ hp) (hcumR _ hp) hDβ hvβ hlocβ
    hEα hregα (hL44 _ hm) (hcumR _ hm) hDα hvα hlocα hAm hAloc hg hgU hgL hgR

end

section
-- from InteractingSLE/Spec/Sec7/Aux37AssemblyStrip.lean
open InteractingSLE.Sec7.Aux37Assembly
open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar chiC fwdHull fwdMap logDerivFwd)
open WangWu (negInv)
open PocketCoord PocketJordan PocketMarks Aux119Bdry LocalSets StripGeom Aux119Nested Aux37Germ StripWall
  StripSideHeightProb
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**No witness frame, almost surely** (Aux. lemma 37's field comparison for the strip system at the deterministic
times `r₀ ≤ s₀`; see the module docstring). -/
theorem ae_noFrame_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    {gU : Ω → DistOn upperHalfPlaneOpens}
    (hgU : IsLocalSetMean (wallUnion β α) (WholeField.centredField h u₀) P gU)
    {gL gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => β ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL t))
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t))
    (hFC : FlatClockStatement P univ (stripExpl W' ζ' β α) g) {r₀ s₀ : ℝ≥0} (hrs : r₀ ≤ s₀) :
    ∀ᵐ ω ∂P, ∀ (Ψ : ℂ → ℂ) (c : Chart), IsFlowChart (α ω) (β ω) r Ψ c →
      changePocket (α ω) (β ω) r ⊆ leftSideOf (range (α ω)) →
      ¬ IsRightWitnessFrame (α ω) (β ω) r (cfHull W' ζ' r₀ ω) (cfHull W' ζ' s₀ ω) (wallUnion β α ω)
          (stripExpl W' ζ' β α r₀ ω) (stripExpl W' ζ' β α s₀ ω) (fun t : ℝ => W' t.toNNReal ω)
          (alphaDrv E θ₁ ω) s₀ (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) s₀)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) s₀) ∧
        ¬ IsLeftWitnessFrame (α ω) (β ω) r (cfHull W' ζ' r₀ ω) (cfHull W' ζ' s₀ ω) (wallUnion β α ω)
          (stripExpl W' ζ' β α r₀ ω) (stripExpl W' ζ' β α s₀ ω) (fun t : ℝ => W' t.toNNReal ω)
          (betaDrv E r θ₂ ω) s₀ (Sec5.GlueCond.cfPosL κ b jumps (W' · ω) s₀)
          (Sec5.GlueCond.cfPosR κ b jumps (W' · ω) s₀) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα := hS.isStagedHistory_alpha hθ₁c
  have hEβ := hS.isStagedHistory_beta hθ₂c r
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁c) (hcumR _ hθ₁c)
      hθ₁c.1 (by linarith [hθ₁c.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂c)
      (fun y hy hyJ => by have := hcumR _ hθ₂c y hy hyJ; linarith) hθ₂c.2 (by linarith [hθ₂c.1])
  have hLdet := hDβ.hdet hregβ u₀ hvβ.ae_isGeneratingTrace
  have hRdet := hDα.hdet hregα u₀ hvα.ae_isGeneratingTrace
  have htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ) := by
    filter_upwards [hvβ.ae_trace, hvα.ae_trace] with ω hL hR
    exact ⟨hL.2.2.2, hR.2.2.2⟩
  have G1 := WordSafe.ae_ownHeights_union_strip h44 hS hcumL hcumR hθ₁c hθ₂c r hregα hregβ hu₀ hvβ hlocβ hvα hlocα
    (measurable_cfHull hS.counterflow r₀) (StripSafe.isLocalSet_cfHull hS.toConst hcumL hcumR u₀ hu₀.1 r₀) (hg r₀) hgU
        hgL hgR
  have G2 := StripSafe.ae_cfGerm_union_strip hS.toConst hcumL hcumR hu₀ hvβ.continuous hvβ.zero hvβ.measurable hLdet
      hlocβ
    hvα.continuous hvα.zero hvα.measurable hRdet hlocα htr s₀ (hg s₀)
  have FC := hFC r₀ trivial s₀ trivial hrs
  filter_upwards [G1, G2, FC, (hg r₀).2.1, (hg s₀).2.1] with ω h1 h2 h3 ⟨vr, hvr, hvrr⟩ ⟨vs, hvs, hvsr⟩ Ψ c hF hCl
  obtain ⟨g1L, g1R⟩ := h1 vr hvr hvrr r Ψ c hF hCl
  have g2 := h2 vs hvs hvsr
  have fc := fun z hz hcomp => h3 vr vs hvr hvrr hvs hvsr z hz hcomp
  refine ⟨fun hfr => ?_, fun hfr => ?_⟩
  · exact false_of_rightFrame (u₀ := u₀) hκ hκ4 hθ₁ g1R
      (fun z₀ hz₀ hε F hF y hy hyJ hy0 hyR => (g2 z₀ hz₀ hε F hF y hy hyJ).2 hy0 hyR) fc hfr
  · exact false_of_leftFrame (u₀ := u₀) hκ hκ4 hθ₂ g1L
      (fun z₀ hz₀ hε F hF y hy hyJ hy0 hyL => (g2 z₀ hz₀ hε F hF y hy hyJ).1 hy0 hyL) fc hfr

end

section
-- from InteractingSLE/Spec/Sec7/Aux37FlatClockProofWire.lean
open InteractingSLE.Sec7.FlatClockProof
open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open LocalSets Aux119Nested Aux37Germ StripWall
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The walls' Lemma 6.2 inputs for the strip system** (as in `WordSafe.ae_noFrame_strip`): the left wall
`β = β^{(r)}` (angle `θ₂`) and the right wall `α` (angle `θ₁`) are determined by the centred field at every time
(from `h44`), and both are transient. -/
theorem strip_walls_inputs (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω)) (u₀ : ℂ → ℝ)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α) :
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    (∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
    (∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ)) := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα := hS.isStagedHistory_alpha hθ₁c
  have hEβ := hS.isStagedHistory_beta hθ₂c r
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hp := StripSys.pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁c) (hcumR _ hθ₁c)
      hθ₁c.1 (by linarith [hθ₁c.2])
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂c)
      (fun y hy hyJ => by have := hcumR _ hθ₂c y hy hyJ; linarith) hθ₂c.2 (by linarith [hθ₂c.1])
  refine ⟨hDβ.hdet hregβ u₀ hvβ.ae_isGeneratingTrace, hDα.hdet hregα u₀ hvα.ae_isGeneratingTrace, ?_⟩
  filter_upwards [hvβ.ae_trace, hvα.ae_trace] with ω hL hR
  exact ⟨hL.2.2.2, hR.2.2.2⟩

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The flat clock for the strip system's walls** `β = β^{(r)}` (left, angle `θ₂`) and `α` (right, angle `θ₁`):
`FlatClockStatement P univ (stripExpl W′ ζ′ β α) g` for every family `g` of versions of the means. -/
theorem flatClockStatement_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t)) :
    FlatClockStatement P univ (stripExpl W' ζ' β α) g := by
  obtain ⟨hβdet, hαdet, htr⟩ := WordSafe.strip_walls_inputs h44 hS hcumL hcumR hθ₁c hθ₂c r hregα hregβ u₀ hvβ hvα
  exact StripSafe.flatClockStatement_stripExpl_of_walls hS.toConst hcumL hcumR hu₀ hvβ.continuous hvβ.zero
      hvβ.measurable hβdet hlocβ
    hvα.continuous hvα.zero hvα.measurable hαdet hlocα htr hg

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Versions of the means of the strip exploration exist** (and it is a local set at every time), for the strip
system's walls `β = β^{(r)}` and `α`. -/
theorem exists_isLocalSetMean_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β α : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β)
    (hlocβ : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P) :
    (∀ t, IsLocalSet (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P) ∧
      ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
        ∀ t, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t) := by
  obtain ⟨hβdet, hαdet, htr⟩ := WordSafe.strip_walls_inputs h44 hS hcumL hcumR hθ₁c hθ₂c r hregα hregβ u₀ hvβ hvα
  exact StripSafe.exists_isLocalSetMean_stripExpl_of_walls hS.toConst hcumL hcumR hu₀ hvβ.continuous hvβ.zero
      hvβ.measurable hβdet
    hlocβ hvα.continuous hvα.zero hvα.measurable hαdet hlocα htr

end

section
-- from InteractingSLE/Spec/Sec7/Aux37FrameAssembly.lean
open InteractingSLE.Sec7.Aux37Frame
open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly LocalSets
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open StripPocketPath in
/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hwit` of `StripPocketPath.pocketWordEvolution_of_stripSystem`** (Aux. lemma 37's exclusion of every rational
witness in the bounded change pocket), exactly in its type, from the flat clock (FC) for each pocket's exploration,
the hypotheses of the proved germs (as in `Aux37Assembly.hwit_hwitI_of_frame`), the consumer's realization data
(the counterflow version `η` and its trace, the walls' reverse visits, the left frontier `β` through the change point,
the avoidance `hav`) and the named analytic input `PocketSideGermStatement`. Angles: `θ₁ ∈ (−π/2, π/2)`,
`θ₂ ∈ (−π/2, π/2]`. -/
theorem hwit_of_sideGerm (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t))
    (hFC : ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω)))
    (hgerm : PocketSideGermStatement κ b jumps P W' E θ₁ θ₂ α Lr η) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  intro q hq s₁ s₂ v v₁ v₂
  by_cases hlt : (s₁ : ℝ) < s₂
  swap
  · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
    rcases hw.1 with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  have hrs : (s₁ : ℝ).toNNReal ≤ (s₂ : ℝ).toNNReal := Real.toNNReal_le_toNNReal hlt.le
  have htrace := StripSafe.ae_isLoewnerTrace_counterflow hS.toConst hcumL hcumR hηtr
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripSafe.ae_counterflow_trace hS.toConst hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  filter_upwards [WordSafe.ae_noFrame_strip h44 hS hcumL hcumR hθ₁ hθ₂ (StripSys.rt q) hregα (hregβ q hq) hu₀ (hvL q hq)
    (hlocL q hq) hvα hlocα (hgU q hq) (hgL q hq) hgR (hg q hq) (hFC q hq) hrs,
    hgerm q hq s₁ s₂ v v₁ v₂, htrace, hreg, hwalls, hwallsL q hq, hβ, hLβ q hq, hav]
    with ω hno hgω htrω hregω hwω hwLω hβω hLβω havω hconf hpos hwit
  have h0 := zero_notMem_closure_of_rightLo_pos hconf hpos
  obtain ⟨⟨Ψ, c, hF⟩, hCl⟩ := exists_isFlowChart_of_cfAvoid hconf hβω hLβω hwω.2 (hηc ω) havω
  obtain ⟨hnoR, hnoL⟩ := hno Ψ c hF hCl
  obtain ⟨hgR', hgL'⟩ := hgω hconf hpos Ψ c hF hCl hwit.2
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htrω.2.2
  have hP := hconf.isReversePocket_of_counterflow h0 htrω.1 htrω.2.1 hW0 hwω.1 hwLω hwω.2
  have he : ∀ t : ℝ≥0, cfHull W' ζ' t ω = negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    cfHull_eq hregω.1 hregω.2.1 hregω.2.2
  have hs₁ : (((s₁ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₁ := by
    refine Real.coe_toNNReal _ (hP.nonneg.trans ?_)
    rcases hwit.1 with h1 | h1
    · exact h1.1
    · exact h1.1
  have hs₂ : (((s₂ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₂ := Real.coe_toNNReal _ ((hs₁ ▸ NNReal.coe_nonneg _).trans hlt.le)
  rcases hwit.1 with hwR | hwL
  · obtain ⟨x, hx, F, hFne, hFG, hgm⟩ := hgR' hwR
    have hwR' : Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcR (α ω) (Lr q ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) ((s₁ : ℝ).toNNReal : ℝ) ((s₂ : ℝ).toNNReal : ℝ)
        v v₁ v₂ := by rw [hs₁, hs₂]; exact hwR
    have hfr := isRightWitnessFrame_of_germ (hFne := hFne) hconf h0 htrω.1 htrω.2.1 hW0 hwω.1 hwLω hwω.2 hF hwR'
      hwit.2 hx hFG hgm
    refine hnoR ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr
  · obtain ⟨x, hx, F, hFne, hFG, hgm⟩ := hgL' hwL
    have hwL' : Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q))
        (cfArcL (α ω) (Lr q ω) (StripSys.rt q)) (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) ((s₁ : ℝ).toNNReal : ℝ) ((s₂ : ℝ).toNNReal : ℝ)
        v v₁ v₂ := by rw [hs₁, hs₂]; exact hwL
    have hfr := isLeftWitnessFrame_of_germ (hFne := hFne) hconf h0 htrω.1 htrω.2.1 hW0 hwω.1 hwLω hwω.2 hF hwL'
      hwit.2 hx hFG hgm
    refine hnoL ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr

end

section
-- from InteractingSLE/Spec/Sec7/Aux37SideAssembly.lean
open InteractingSLE.Sec7.Aux37Side
open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The side germ statement for the strip system** (`Aux37Frame.PocketSideGermStatement`), from the counterflow's
trace, the walls' reverse visits and the walls' own Loewner traces. -/
theorem pocketSideGermStatement_of_traces
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hownα : ∀ᵐ ω ∂P, IsLoewnerTrace (alphaDrv E θ₁ ω) (Lemma71I.realPath (α ω)) ∧ Continuous (alphaDrv E θ₁ ω) ∧
      alphaDrv E θ₁ ω 0 = 0)
    (hownL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsLoewnerTrace (betaDrv E (StripSys.rt q) θ₂ ω) (Lemma71I.realPath (Lr q ω)) ∧
      Continuous (betaDrv E (StripSys.rt q) θ₂ ω) ∧ betaDrv E (StripSys.rt q) θ₂ ω 0 = 0) :
    PocketSideGermStatement κ b jumps P W' E θ₁ θ₂ α Lr η := by
  intro q hq s₁ s₂ v v₁ v₂
  filter_upwards [StripSafe.ae_isLoewnerTrace_counterflow hS.toConst hcumL hcumR hηtr, hwalls, hwallsL q hq, hownα,
      hownL q hq]
    with ω htr hw hwL hα hL hconf hpos Ψ c hF _ _
  have h0 := zero_notMem_closure_of_rightLo_pos hconf hpos
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htr.2.2
  have hs₂ : ∀ {A : ℝ → ℂ}, Aux37Attach.IsAttachWitness (η ω) (cfPocket (α ω) (Lr q ω) (StripSys.rt q)) A
      (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 1))
      (firstHit (η ω) (cfArcR (α ω) (Lr q ω) (StripSys.rt q) 0)) s₁ s₂ v v₁ v₂ → (0 : ℝ) ≤ s₂ := fun hwit =>
    ((Real.sInf_nonneg fun _ hx => hx.1).trans hwit.1).trans hwit.2.1.le
  refine ⟨fun hwit => ?_, fun hwit => ?_⟩
  · exact isRightSideGerm_of_witness hconf h0 htr.1 htr.2.1 hW0 hw.1 hwL hw.2 hF hwit hα.1 hα.2.1 hα.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (Real.coe_toNNReal _ (hs₂ hwit))
  · exact isLeftSideGerm_of_witness hconf h0 htr.1 htr.2.1 hW0 hw.1 hwL hw.2 hF hwit hL.1 hL.2.1 hL.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htr.2.1 (hs₂ hwit) i)
      (Real.coe_toNNReal _ (hs₂ hwit))

end

section
-- from InteractingSLE/Spec/Sec7/Aux37SideAssembly.lean
open InteractingSLE.Sec7.Aux37Side
open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
variable {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The right wall's own trace**: almost surely `α` is a continuous Loewner trace of its own continuous driver (from
the version and the infinite lifetimes of the field-determined pieces). -/
theorem ae_ownTrace_alpha (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    {α : Ω → ℝ≥0 → ℂ} (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (alphaDrv E θ₁ ω) (Lemma71I.realPath (α ω)) ∧ Continuous (alphaDrv E θ₁ ω) ∧
      alphaDrv E θ₁ ω 0 = 0 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEα := hS.isStagedHistory_alpha hθ₁c
  have hm := StripSys.neg_pi_div_two_mem_Icc
  have hDα : IsDetTwoPiece P h (E (StripSys.alphaSpec θ₁)) :=
    isDetTwoPiece_of_heights h44 hκ hκ4 hb hh hEα hregα (hL44 _ hm) (hcumR _ hm) (hL44 _ hθ₁c) (hcumR _ hθ₁c)
      hθ₁c.1 (by linarith [hθ₁c.2])
  filter_upwards [hvα.ae_trace, hDα.ae_lifetimes] with ω htr hl
  obtain ⟨hc, hc0⟩ := continuous_catPath_of_isRegularDriver (hregα 0 ω) (hregα 1 ω) hl.1 hl.2 1
  refine ⟨isLoewnerTrace_of_isGeneratingTrace htr.1, hc.comp continuous_real_toNNReal, ?_⟩
  show catPath _ 1 _ (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero]
  exact hc0

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The left wall's own trace** (as `WordSafe.ae_ownTrace_alpha`, for `β^{(q)}`). -/
theorem ae_ownTrace_beta (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ j ω, IsRegularDriver (E (StripSys.betaSpec r θ₂) j ω))
    {β : Ω → ℝ≥0 → ℂ} (hvβ : IsWallVersion P (E (StripSys.betaSpec r θ₂)) r β) :
    ∀ᵐ ω ∂P, IsLoewnerTrace (betaDrv E r θ₂ ω) (Lemma71I.realPath (β ω)) ∧ Continuous (betaDrv E r θ₂ ω) ∧
      betaDrv E r θ₂ ω 0 = 0 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  have hL44 : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps →
      b y + a * chiC κ ≤ -sleLambda κ + π * chiC κ := fun a ha y hy hyJ => by
    have := hcumL a ha y hy hyJ
    linarith
  have hEβ := hS.isStagedHistory_beta hθ₂c r
  have hp := StripSys.pi_div_two_mem_Icc
  have hDβ : IsDetTwoPiece P h (E (StripSys.betaSpec r θ₂)) :=
    isDetTwoPiece_of_heights_refl h44 hκ hκ4 hb hh hEβ hregβ (hL44 _ hp) (hcumR _ hp) (hcumL _ hθ₂c)
      (fun y hy hyJ => by have := hcumR _ hθ₂c y hy hyJ; linarith) hθ₂c.2 (by linarith [hθ₂c.1])
  filter_upwards [hvβ.ae_trace, hDβ.ae_lifetimes] with ω htr hl
  obtain ⟨hc, hc0⟩ := continuous_catPath_of_isRegularDriver (hregβ 0 ω) (hregβ 1 ω) hl.1 hl.2 r
  refine ⟨isLoewnerTrace_of_isGeneratingTrace htr.1, hc.comp continuous_real_toNNReal, ?_⟩
  show catPath _ r _ (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero]
  exact hc0

end

section
-- from InteractingSLE/Spec/Sec7/Aux37SideAssembly.lean
open InteractingSLE.Sec7.Aux37Side
open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open StripPocketPath in
/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hwit` of `StripPocketPath.pocketWordEvolution_of_stripSystem`** (Aux. lemma 37's exclusion of every rational
witness in the bounded change pocket), exactly in its type, from the flat clock (FC) and the consumer's realization
data: the binders of `WordSafe.hwit_of_sideGerm` without `PocketSideGermStatement`, which is proved
(`WordSafe.pocketSideGermStatement_of_traces`). Angles: `θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`. -/
theorem hwit_of_flatClock (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t))
    (hFC : ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ :=
  WordSafe.hwit_of_sideGerm h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀ hvα hlocα hvL hlocL hgU hgL hgR hg hFC hηc hηtr
      hwalls
    hwallsL hβ hLβ hav (WordSafe.pocketSideGermStatement_of_traces hS hcumL hcumR hηtr hwalls hwallsL
      (WordSafe.ae_ownTrace_alpha h44 hS hcumL hcumR hθ₁ hregα hvα)
      fun q hq => WordSafe.ae_ownTrace_beta h44 hS hcumL hcumR hθ₂ (StripSys.rt q) (hregβ q hq) (hvL q hq))

end

section
-- from InteractingSLE/Spec/Sec7/Aux37SideInfFrame.lean
open InteractingSLE.Sec7.Aux37Side
open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real
open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O Aux37Frame StripPocketPath
open MeasureTheory
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)
open scoped ENNReal
open PocketMarks Aux119Nested Aux37Germ StripWall StripSideHeightProb Aux37Assembly LocalSets
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hwitI` of `StripPocketPath.pocketWordEvolution_of_stripSystem`** (Aux. lemma 37's exclusion of every rational
witness in the change pocket at the flow seed, `rightLo = 0`), exactly in its type, from the flat clock (FC) and the
consumer's realization data (as `WordSafe.hwit_of_flatClock`, with both visits of the left walls in `hwallsL`). Angles:
`θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`. -/
theorem hwitI_of_flatClock (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t))
    (hFC : ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  intro q hq s₁ s₂ v v₁ v₂
  by_cases hlt : (s₁ : ℝ) < s₂
  swap
  · refine Eventually.of_forall fun ω _ _ hw => hlt ?_
    rcases hw.1 with h1 | h1
    · exact h1.2.1
    · exact h1.2.1
  have hrs : (s₁ : ℝ).toNNReal ≤ (s₂ : ℝ).toNNReal := Real.toNNReal_le_toNNReal hlt.le
  have htrace := StripSafe.ae_isLoewnerTrace_counterflow hS.toConst hcumL hcumR hηtr
  have hreg : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous fun t => W' t ω := by
    filter_upwards [StripSafe.ae_counterflow_trace hS.toConst hcumL hcumR] with ω hω
    exact ⟨hω.1, hω.2.2.1, hω.2.1⟩
  filter_upwards [WordSafe.ae_noFrame_strip h44 hS hcumL hcumR hθ₁ hθ₂ (StripSys.rt q) hregα (hregβ q hq) hu₀ (hvL q hq)
    (hlocL q hq) hvα hlocα (hgU q hq) (hgL q hq) hgR (hg q hq) (hFC q hq) hrs, htrace, hreg, hwalls, hwallsL q hq,
    hβ, hLβ q hq, hav, WordSafe.ae_ownTrace_alpha h44 hS hcumL hcumR hθ₁ hregα hvα,
    WordSafe.ae_ownTrace_beta h44 hS hcumL hcumR hθ₂ (StripSys.rt q) (hregβ q hq) (hvL q hq)]
    with ω hno htrω hregω hwω hwLω hβω hLβω havω hα hL hconf hpos hwit
  obtain ⟨⟨Ψ, c, hF⟩, hCl⟩ := exists_isFlowChart_of_cfAvoid hconf hβω hLβω hwω.2 (hηc ω) havω
  obtain ⟨hnoR, hnoL⟩ := hno Ψ c hF hCl
  have hW0 : (fun s : ℝ => W' s.toNNReal ω) 0 = 0 := by simpa using htrω.2.2
  have he : ∀ t : ℝ≥0, cfHull W' ζ' t ω = negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    cfHull_eq hregω.1 hregω.2.1 hregω.2.2
  have hs₁0 : (0 : ℝ) ≤ s₁ := by
    rcases hwit.1 with h1 | h1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
    · exact (Real.sInf_nonneg fun _ hx => hx.1).trans h1.1
  have hs₁ : (((s₁ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₁ := Real.coe_toNNReal _ hs₁0
  have hs₂ : (((s₂ : ℝ).toNNReal : ℝ≥0) : ℝ) = s₂ := Real.coe_toNNReal _ (hs₁0.trans hlt.le)
  rcases hwit.1 with hwR | hwL
  · have hfr := isRightWitnessFrame_of_inf hconf hpos htrω.1 htrω.2.1 hW0 hwω.1 hwLω.1 hwω.2 hwLω.2 hF hwR hwit.2
      hα.1 hα.2.1 hα.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      hs₁ hs₂
    refine hnoR ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr
  · have hfr := isLeftWitnessFrame_of_inf hconf hpos htrω.1 htrω.2.1 hW0 hwω.1 hwLω.1 hwω.2 hwLω.2 hF hwL hwit.2
      hL.1 hL.2.1 hL.2.2
      (fun i => cfPosR_ge (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      (fun i => cfPosL_le (κ := κ) (b := b) (jumps := jumps) (w := fun t => W' t ω) htrω.2.1 (hs₁0.trans hlt.le) i)
      hs₁ hs₂
    refine hnoL ?_
    simp only [stripExpl, wallUnion, he]
    exact hfr

end

section
-- from InteractingSLE/Spec/Sec7/Aux37FlatClockProofWire.lean
open InteractingSLE.Sec7.FlatClockProof
open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open LocalSets Aux119Nested Aux37Germ StripWall
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The flat clock for the family `β^{(q)} = Lr q`** (`q ∈ ℚ>0`, stage time `rt q`), exactly the input `hFC` of
`WordSafe.hwit_of_flatClock` and `WordSafe.hwitI_of_flatClock`. -/
theorem flatClockStatement_strip_rat (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t)) :
    ∀ q : ℚ, 0 < q → FlatClockStatement P univ (stripExpl W' ζ' (Lr q) α) (g q) := fun q hq =>
  WordSafe.flatClockStatement_strip h44 hS hcumL hcumR hθ₁c hθ₂c (StripSys.rt q) hregα (hregβ q hq) hu₀ (hvL q hq)
    (hlocL q hq) hvα hlocα (hg q hq)

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Versions of the means for the family `β^{(q)} = Lr q`** (`q ∈ ℚ>0`): a family `g` as in the input `hg` of
`WordSafe.hwit_of_flatClock` and `WordSafe.hwitI_of_flatClock`. -/
theorem exists_isLocalSetMean_strip_rat (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2)) (hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P) :
    ∃ g : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g q t) := by
  have hex : ∀ q : ℚ, ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (stripExpl W' ζ' (Lr q) α t) (WholeField.centredField h u₀) P (g t) := fun q => by
    by_cases hq : 0 < q
    · obtain ⟨-, g, hg⟩ := WordSafe.exists_isLocalSetMean_strip h44 hS hcumL hcumR hθ₁c hθ₂c (StripSys.rt q) hregα
        (hregβ q hq) hu₀ (hvL q hq) (hlocL q hq) hvα hlocα
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hq⟩
  choose g hg using hex
  exact ⟨g, fun q hq t => hg q hq t⟩

end

section
-- from InteractingSLE/Spec/Sec7/Aux37FlatClockProofHwit.lean
open InteractingSLE.Sec7.FlatClockProof
open MeasureTheory Set Metric Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks Aux119Bdry Aux119Nested Aux37Germ StripWall
  StripSideHeightProb StripPocketPath Aux37Assembly Aux37Frame LocalSets
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hwit` without the flat clock and the exploration means**: `WordSafe.hwit_of_flatClock` with the versions `g`
of the means of the strip exploration supplied by `WordSafe.exists_isLocalSetMean_strip_rat` and `hFC` discharged by
`WordSafe.flatClockStatement_strip_rat`; the remaining field inputs are the walls' means `gU`, `gL`, `gR`. Angles
`θ₁ ∈ (−π/2, π/2)`, `θ₂ ∈ (−π/2, π/2]`. -/
theorem hwit_of_wallMeans (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        ¬ IsPocketWitness (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨g, hg⟩ := WordSafe.exists_isLocalSetMean_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁)
    (Ioc_subset_Icc_self hθ₂) hregα hregβ hu₀ hvα hlocα hvL hlocL
  exact WordSafe.hwit_of_flatClock h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀ hvα hlocα hvL hlocL hgU hgL hgR hg
    (WordSafe.flatClockStatement_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) hregα
      hregβ hu₀ hvα hlocα hvL hlocL hg) hηc hηtr hwalls hwallsL hβ hLβ hav

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hwitI` without the flat clock and the exploration means**: `WordSafe.hwitI_of_flatClock` with `g` from
`WordSafe.exists_isLocalSetMean_strip_rat` and `hFC` from `WordSafe.flatClockStatement_strip_rat`. Angles `θ₁ ∈ (−π/2,
    π/2)`,
`θ₂ ∈ (−π/2, π/2]`. -/
theorem hwitI_of_wallMeans (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' E)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hlocα : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (hvL : ∀ q : ℚ, 0 < q → IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q))
    (hlocL : ∀ q : ℚ, 0 < q → Sec6.IsEntranceHistoryLocal (Lr q) (WholeField.centredField h u₀) P)
    {gU : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hgU : ∀ q : ℚ, 0 < q → IsLocalSetMean (wallUnion (Lr q) α) (WholeField.centredField h u₀) P (gU q))
    {gL : ℚ → ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgL : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0,
      IsLocalSetMean (fun ω => Lr q ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gL q t))
    {gR : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgR : ∀ t : ℝ≥0, IsLocalSetMean (fun ω => α ω '' Icc 0 t ∩ H) (WholeField.centredField h u₀) P (gR t))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
    (hβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω))
    (hLβ : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, Lr q ω (StripSys.rt q) = β ω (StripSys.rt q))
    (hav : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → negInv (η ω q) ∉ leftSideOf (range (β ω))) :
    ∀ q : ℚ, 0 < q → ∀ s₁ s₂ v v₁ v₂ : ℚ, ∀ᵐ ω ∂P, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) →
      rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        ¬ IsPocketWitnessInf (α ω) (Lr q ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
  obtain ⟨g, hg⟩ := WordSafe.exists_isLocalSetMean_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁)
    (Ioc_subset_Icc_self hθ₂) hregα hregβ hu₀ hvα hlocα hvL hlocL
  exact WordSafe.hwitI_of_flatClock h44 hS hcumL hcumR hθ₁ hθ₂ hregα hregβ hu₀ hvα hlocα hvL hlocL hgU hgL hgR hg
    (WordSafe.flatClockStatement_strip_rat h44 hS hcumL hcumR (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) hregα
      hregβ hu₀ hvα hlocα hvL hlocL hg) hηc hηtr hwalls hwallsL hβ hLβ hav

end

section
-- from InteractingSLE/Spec/Sec7/StripMarks513.lean
open InteractingSLE.Sec7.StripMarks
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real
open WholeField PocketWordIn StripSysField Wire
open Sec4 Sec5 Sec5.Prop513Schedule Sec5.Prop513Target Sec5.Prop513TreeExtract
  Sec5.Prop513Asm Sec5.Prop59Sched Sec5.Prop59Stage Sec5.Prop59System Sec5.StripRevVisit
  Sec5.Prop59Nodes Sec5.Prop513Bridge
open Restart Exist Exist.Staged Exist.StagedLaw
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The chosen counterflow field of the strip system is the field of the angle-0 flow line of the explicit
counterflow word** (FD11.1, FD12.1–FD12.2): `Theorem14.GW2Cone.isFlowLineDriver_counterflowData`, with its transported
field identified with `(counterflowObjects hS.counterflow).field` (uniqueness of the transport through the conformal
infinity-source chart, and the translation by `0` with constant `0` is the identity). -/
theorem stripCounterflow_isFlowLineDriver (hS : IsTwoAngleStripSystem κ b J P h W ζ E) :
    IsFlowLineDriver (16 / κ) (counterflowData κ b) (counterflowJumps J) 0 P
      (counterflowObjects hS.counterflow).field W ζ := by
  obtain ⟨h', htr', hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hS.kappa_pos hS.boundaryData
    hS.gff hS.counterflow
  obtain ⟨hT, hTr, -, -⟩ := counterflowObjects_spec hS.counterflow
  have e : h' = (counterflowObjects hS.counterflow).field := by
    funext ω
    rw [IsChartTransport.unique Chart.isConformal_infinitySourceChart (htr' ω) (hT ω)]
    exact (Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (hTr ω)).symm
  rw [← e]
  exact hfl

end

section
-- from InteractingSLE/Spec/Sec7/StripPocketPathFinal.lean
open InteractingSLE.Sec7.StripPocketPath
open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen PocketLeftFrontier
  PocketCoupling StripSideHeightProb
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The strip system's counterflow is transient in the chart `m`** (Aux. lemma 7 at `κ′ = 16/κ` for its admissible
word, Remark 4.8 (b)): every version `η` of its trace tends to `∞` almost surely. -/
theorem ae_transient_counterflow (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ᵐ ω ∂P, Tendsto (fun t => ‖η ω t‖) atTop atTop := by
  have hκ := hS.kappa_pos
  have hb := hS.boundaryData
  obtain ⟨h', -, hfl⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hS.gff hS.counterflow
  obtain ⟨h'', 𝓕₂, VL₂, VR₂, B₂, -, hC'⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hbd := counterflowData_bounds_off hκ (g := b) (J := jumps)
    (fun x hx hxJ => by have := hcumL _ StripSys.neg_pi_div_two_mem_Icc x hx hxJ; linarith)
    (fun x hx hxJ => by have := hcumR _ StripSys.pi_div_two_mem_Icc x hx hxJ; linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_flowLine hk'
    (StripSysField.isPiecewiseConstant_counterflowData κ hb) hbd.1 hbd.2
  have hF' := Theorem15.isOrderedForceWord_flowLine (StripSysField.counterflowData κ b)
    (StripSysField.counterflowJumps jumps) 0
  filter_upwards [haux7 _ _ _ _ P 𝓕₂ W' VL₂ VR₂ B₂ ζ' hF' hadm hC'.1, hηtr] with ω hω hη
  have h1 := hω.2.2 _ hη
  have h2 : Tendsto (fun t : ℝ => ‖η ω (t.toNNReal : ℝ)‖) atTop atTop := h1.comp tendsto_real_toNNReal_atTop
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.coe_toNNReal _ ht]

end

section
-- from InteractingSLE/Spec/Sec7/StripPocketPathLate.lean
open InteractingSLE.Sec7.StripPocketPath
open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open StripSideHeightProb StripGeom LocalSets
open Exist.Staged (IsRegularDriver)
open Restart.StagedEntrance (frozenPath continuous_frozenPath)
open PocketJordan PocketMeas
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The driver of `β = η_{π/2}` is field-determined** (R48-safe): almost surely its lifetime is infinite and it is
`AdmCode.admDrv (π/2) (c₀, h)` for a sorted word `c₀` of the data `b`. -/
theorem exists_ae_leftExtremal_eq_admDrv (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∃ c₀ : Restart.BoundaryWord, ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧
      (Es StripSys.leftExtremalSpec 0 ω).1 =
        (AdmCode.admDrv h44 hS.kappa_pos hS.kappa_lt_four (π / 2) (c₀, h ω)).1 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  obtain ⟨hL0, hR0⟩ := heights_pi_div_two hκ hκ4 hcumL hcumR
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have h44c : Sec4.Cond44 κ (flowLineRhoL κ c₀.fn c₀.jumps 0 (π / 2))
      (flowLineRhoR κ c₀.fn c₀.jumps 0 (π / 2)) := by
    refine StripDet.cond44_flowLine_of_heights hκ c₀.isPiecewiseConstantBoundaryData (π / 2)
      (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hL0 y hy hyJ
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hR0 y hy hyJ
  have hEd := (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
    (fun y hy => hc₀ y hy)).2 (isFlowLineDriver_leftExtremal hκ hb hS.gff hS.isStagedHistory_leftExtremal)
  refine ⟨c₀, ?_⟩
  filter_upwards [AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 (π / 2) c₀ h44c hEd] with ω h2
  refine ⟨h2.1, funext fun t => ?_⟩
  exact (h2.2.2 t (by rw [h2.1]; exact ENNReal.coe_lt_top)).symm

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Lemma 6.2's determination input for `β = η_{π/2}`**: every version of `β` is, at every time, almost surely a
Borel function of the centred field `h − 𝔥₀` (LP11's reconstruction of the field-determined driver). -/
theorem hdet_leftExtremal (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω)) (u₀ : ℂ → ℝ) {β : Ω → ℝ≥0 → ℂ}
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω)) :
    ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := by
  obtain ⟨c₀, hD⟩ := WordSafe.exists_ae_leftExtremal_eq_admDrv h44 hS hcumL hcumR
  intro t
  set c : DistOn upperHalfPlaneOpens :=
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hc
  have hadd : Measurable fun g : DistOn upperHalfPlaneOpens => g + c := Coupling.measurable_add_distOnConst c
  refine ⟨fun g => LP.traceAt t (AdmCode.admDrv h44 hS.kappa_pos hS.kappa_lt_four (π / 2) (c₀, g + c)).1, ?_, ?_⟩
  · exact (LP.measurable_traceAt t).comp (measurable_fst.comp
      ((AdmCode.measurable_admDrv h44 hS.kappa_pos hS.kappa_lt_four (π / 2)).comp (measurable_const.prodMk hadd)))
  · filter_upwards [hD, hβtr] with ω hω hη
    have hcent : WholeField.centredField h u₀ ω + c = h ω := by
      simp only [WholeField.centredField, hc, sub_add_cancel]
    simp only [hcent, ← hω.2]
    have hcc := StripWall.continuous_of_isRegularDriver (hregE ω) hω.1
    exact (LP.traceAt_eq_of_isGeneratingTrace hη hcc.continuousOn (hregE ω).2.1 ENNReal.coe_lt_top).symm

end

section
-- from InteractingSLE/Spec/Sec7/StripPocketPathWalls.lean
open InteractingSLE.Sec7.StripPocketPath
open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open StripSideHeightProb
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`β = η_{π/2}` of the strip system has a simple transient trace** almost surely (Aux. lemma 130's height
choice). -/
theorem ae_simple_trace_leftExtremal_strip (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ) :
    ∀ᵐ ω ∂P, (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧ ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ η ∧ Injective η ∧ (∀ t, 0 < t → η t ∈ H) ∧
        Tendsto (fun t => ‖η t‖) atTop atTop := by
  obtain ⟨hL0, hR0⟩ := heights_pi_div_two hS.kappa_pos hS.kappa_lt_four hcumL hcumR
  exact ae_simple_trace_leftExtremal hS.kappa_pos hS.kappa_lt_four hS.boundaryData hS.gff
    hS.isStagedHistory_leftExtremal hL0 hR0

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Every version of `β = η_{π/2}` is almost surely a simple proper curve** (spec p. 410). -/
theorem ae_isSimpleProper_leftExtremal (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    (hregE : ∀ ω, IsRegularDriver (Es StripSys.leftExtremalSpec 0 ω))
    {β : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω)) :
    ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (β ω) :=
  ae_isSimpleProper_of_simple_trace hregE (WordSafe.ae_simple_trace_leftExtremal_strip hS hcumL hcumR) hβc hβ0 hβtr

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
The two first pieces (of `β^{(r)}` and of `β`) are almost surely the same field-determined driver: both are
`AdmCode.admDrv (π/2) (c₀, h)` with infinite lifetime. -/
theorem ae_driver_betaSpec_eq_leftExtremal (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0) :
    ∀ᵐ ω ∂P, (Es (StripSys.betaSpec r θ₂) 0 ω).2 = ⊤ ∧ (Es StripSys.leftExtremalSpec 0 ω).2 = ⊤ ∧
      (Es (StripSys.betaSpec r θ₂) 0 ω).1 = (Es StripSys.leftExtremalSpec 0 ω).1 := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  obtain ⟨hL0, hR0⟩ := heights_pi_div_two hκ hκ4 hcumL hcumR
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have hcw : ∀ {Wd : ℝ≥0 → Ω → ℝ} {ζd : Ω → ℝ≥0∞},
      IsFlowLineDriver κ b jumps (π / 2) P h Wd ζd → IsFlowLineDriver κ c₀.fn c₀.jumps (π / 2) P h Wd ζd :=
    fun hfl => (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps
      (fun y hy => hc₀ y hy)).2 hfl
  have h44c : Sec4.Cond44 κ (flowLineRhoL κ c₀.fn c₀.jumps 0 (π / 2))
      (flowLineRhoR κ c₀.fn c₀.jumps 0 (π / 2)) := by
    refine StripDet.cond44_flowLine_of_heights hκ c₀.isPiecewiseConstantBoundaryData (π / 2)
      (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hL0 y hy hyJ
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hR0 y hy hyJ
  have hβd := hcw (StripWall.isFlowLineDriver_stage_zero hκ hb hS.gff (hS.isStagedHistory_beta hθ₂ r))
  have hEd := hcw (isFlowLineDriver_leftExtremal hκ hb hS.gff hS.isStagedHistory_leftExtremal)
  filter_upwards [AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 (π / 2) c₀ h44c hβd,
    AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 (π / 2) c₀ h44c hEd] with ω h1 h2
  refine ⟨h1.1, h2.1, funext fun t => ?_⟩
  rw [← h1.2.2 t (by rw [h1.1]; exact ENNReal.coe_lt_top), ← h2.2.2 t (by rw [h2.1]; exact ENNReal.coe_lt_top)]

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The common prefix** ("Its prefix through `r` … unchanged", p. 411): a version of `β^{(r)} = η^{r,∞}_{π/2,θ₂}`
agrees almost surely with the version of `β = η_{π/2}` on `[0, r]`. -/
theorem ae_eq_leftExtremal_of_le (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hS : IsTwoAngleStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Icc (-(π / 2)) (π / 2)) (r : ℝ≥0)
    (hregβ : ∀ ω, IsRegularDriver (Es (StripSys.betaSpec r θ₂) 0 ω))
    {L β : Ω → ℝ≥0 → ℂ}
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (Es (StripSys.betaSpec r θ₂) 0 ω).1 r
      (Es (StripSys.betaSpec r θ₂) 1 ω).1) ⊤ (L ω))
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ r → L ω t = β ω t := by
  filter_upwards [WordSafe.ae_driver_betaSpec_eq_leftExtremal h44 hS hcumL hcumR hθ₂ r, hLtr, hβtr]
    with ω hd hL hβ t ht
  obtain ⟨hζ, -, he⟩ := hd
  have hL' : IsGeneratingTrace (Es (StripSys.betaSpec r θ₂) 0 ω).1 r (L ω) :=
    IsGeneratingTrace.of_eqOn_lt hL fun s hs => (catPath_of_le (ENNReal.coe_lt_coe.1 hs).le).symm
  have hβ' : IsGeneratingTrace (Es (StripSys.betaSpec r θ₂) 0 ω).1 r (β ω) :=
    LP.isGeneratingTrace_mono (he ▸ hβ) le_top
  have hcont : ContinuousOn (Es (StripSys.betaSpec r θ₂) 0 ω).1 {s : ℝ≥0 | (s : ℝ≥0∞) < r} :=
    (StripWall.continuous_of_isRegularDriver (hregβ ω) hζ).continuousOn
  exact IsGeneratingTrace.eq_of_le hL' hβ' hcont (hregβ ω).2.1 (ENNReal.coe_le_coe.2 ht)

end

section
-- from InteractingSLE/Spec/Sec5/RestartGenWalls.lean
open InteractingSLE.Sec5 InteractingSLE.Sec5.RestartGen
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open WangWu (negInv negInv_negInv')
open Prop411Q (IsFirstHitQ)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.StripSideHeightProb (catPath catPath_of_le)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**The unchanged extremal wall `β = η_{π/2}`** (a one-angle wall: the left boundary of the counterflow): the
rational first-exit law from the landed Lemma 4.7 alone. -/
theorem ae_isFirstHitQ_leftExtremal (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {β : Ω → ℝ≥0 → ℂ} (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E Sec7.StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (β ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  obtain ⟨hf, F, VL, VR, B, ht, hC⟩ := Sec7.StripPocketPath.isFlowLineDriver_leftExtremal hκ hS.boundaryData
    hS.gff hS.isStagedHistory_leftExtremal
  have hβ : IsFlowLine κ b J 0 (π / 2) P h β (fun ω => (E Sec7.StripSys.leftExtremalSpec 0 ω).2) := by
    refine ⟨hf, F, fun t ω => (E Sec7.StripSys.leftExtremalSpec 0 ω).1 t, VL, VR, B, ht, hC, ?_⟩
    filter_upwards [hβtr, WordSafe.ae_simple_trace_leftExtremal_strip hS hleft hright]
      with ω htr hreg
    simpa only [hreg.1, Complex.ofReal_zero, sub_zero] using htr
  exact ae_isFirstHitQ_of_isFlowLine_pi_div_two h47 href hκ hκ4 hS.boundaryData
    (heights_of_cum hκ hκ4 hleft hright Sec7.StripSys.pi_div_two_mem_Icc) hS.gff hS.counterflow hS.lifetime hη hβ q hq

end

section
-- from InteractingSLE/Spec/Sec5/RestartGenConsumers.lean
open InteractingSLE.Sec5 InteractingSLE.Sec5.RestartGen
open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.StripSideHeightProb (catPath)
open Exist.Staged (IsRegularDriver)
variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`hfirstE`** (the unchanged extremal wall `β = η_{π/2}`): from the landed Lemma 4.7 alone. -/
theorem hfirstE_of_restartGen (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {β : Ω → ℝ≥0 → ℂ} (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E Sec7.StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (β ω)) (η ω) q := by
  intro q hq
  filter_upwards [WordSafe.ae_isFirstHitQ_leftExtremal (η := fun ω (t : ℝ≥0) => η ω t) h47 href hS hleft hright hβtr
      hηtr
    q hq] with ω hω
  exact isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω

end

end InteractingSLE.Sec7.WordSafe
