/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartGenOne
import InteractingSLE.Spec.Sec7.StripPocketPathWalls
import InteractingSLE.Spec.Sec7.StripWallStage0
import InteractingSLE.Spec.Sec7.Aux37WallsConst
import InteractingSLE.Spec.Sec7.PocketWordInWalls

/-!
# The restart law for the walls of the strip system

Packet PROVE-RESTART-GEN. The pocket word (Aux. 130, pp. 410–412; `Sec7.PocketWordIn`, `Sec7.WallsPath`) and R.7
(`Sec7.WallsPath.r7PocketStopStatement_of_stripSystem_path_prop74`) take, for each wall `R` of the strip system, the
**rational first-exit law**: at every positive rational own time `q`, the counterflow `R ∘ η` first contacts
`R((0, q])` at `R(q)` (Lemma 5.7's first exit, p. 138). The walls are staged flow lines of the strip field `h`:
one-angle walls (`R7Aux131.constSpec θ`, `Sec7.StripSys.leftExtremalSpec`) and two-angle walls
(`Sec7.StripSys.twoAngleSpec θ₀ t₀ θ`: angle `θ₀` for own time `t₀`, then `θ`; `alphaSpec`, `betaSpec`).

**The general law, stated once** (`SwitchedWallFirstHitStatement`): for every two-angle wall of every strip system
with the height choice of Aux. 130, the first exit at rational times **after the switch** `t₀`. It is the
conditional law of the counterflow given an angle-varying flow-line prefix (Lemma 5.7 with `ℓ = 2`, Figure 5.5,
right panel). Everything else is proved here:

* **before the switch** the wall is the angle-`θ₀` flow line of `h` (`ae_eq_firstPiece_of_le`), so the one-angle law
  (`RestartGenOne`, Lemma 4.7 on the glued space transferred to the strip frame) applies:
  `ae_isFirstHitQ_twoAngle_le`;
* the unchanged extremal wall `β = η_{π/2}` (`ae_isFirstHitQ_leftExtremal`) and the constant-angle walls of R.7
  (`ae_isFirstHitQ_const`) are one-angle walls: no switched law is needed;
* `ae_isFirstHitQ_twoAngle`: all rational times of a two-angle wall;
* the consumers' exact first-exit binders: `hfirstR_of_restartGen`, `hfirstE_of_restartGen`, `hfirstL_of_restartGen`
  (`PocketWordIn.pocketWordEvolution_of_stripSystem_firstHit`), `hfirstα_path_of_restartGen`,
  `hfirstL_path_of_restartGen` (`WallsPath.pocketWordEvolution_of_stripSystem_path`), and
  `hfirstR7_of_restartGen` (R.7, both walls), with the adapter `isFirstHitPoint_of_isFirstHitQ` to the
  `Sec4.IsFirstHitPoint` form.

The one-angle inputs are `RestartGen.Lemma47QHitTStatement θ` at the angles used (at `π/2` the landed
`Prop411Q.Lemma47QHitStatement`, `lemma47QHitTStatement_pi_div_two`) and the §4.2 reference. R48: nothing uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.RestartGen

open WangWu (negInv negInv_negInv')
open Prop411Q (IsFirstHitQ)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.StripSideHeightProb (catPath catPath_of_le)

/-! ### Deterministic adapters -/

/-- **The first-contact property depends only on the flow path on `(0, q]` and the counterflow at positive
times.** -/
theorem isFirstHitQ_congr {γ γ' β β' : ℝ → ℂ} {q : ℝ} (hq : 0 < q) (hγ : ∀ s ∈ Ioc (0 : ℝ) q, γ s = γ' s)
    (hβ : ∀ u : ℝ, 0 < u → β u = β' u) (h : IsFirstHitQ γ β q) : IsFirstHitQ γ' β' q := by
  obtain ⟨u, hu0, hu, hbefore⟩ := h
  have himg : γ '' Ioc 0 q = γ' '' Ioc 0 q := image_congr hγ
  refine ⟨u, hu0, ?_, fun v hv => ?_⟩
  · rw [← hβ u hu0, hu, hγ q ⟨hq, le_rfl⟩]
  · rw [← hβ v hv.1, ← himg]
    exact hbefore v hv

/-- **The first-contact property in the form of `Sec4.IsFirstHitPoint`** (the form of `WallsPath`'s binders): the
chart-`R` counterflow `η` first hits the inverted wall prefix `R(γ((0, q]))` at `R(γ(q))`, if `η(0) = 0` and the wall
is nonzero at positive times. -/
theorem isFirstHitPoint_of_isFirstHitQ {γ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {q : ℝ≥0} (hq : 0 < q)
    (hγ0 : ∀ t : ℝ≥0, 0 < t → γ t ≠ 0) (hη0 : η 0 = 0) (h : IsFirstHitQ (Sec7.Lemma71I.realPath γ) η q) :
    ∃ T : ℝ, Sec4.IsFirstHitPoint η T (negInv '' (γ '' Ioc 0 q)) (negInv (γ q)) := by
  obtain ⟨u, hu0, hu, hbefore⟩ := h
  have hγq : Sec7.Lemma71I.realPath γ (q : ℝ) = γ q := by
    simp only [Sec7.Lemma71I.realPath, Real.toNNReal_coe]
  refine ⟨u, u, ⟨hu0.le, le_rfl⟩, ?_, ⟨γ q, ⟨q, ⟨hq, le_rfl⟩, rfl⟩, rfl⟩, fun v hv hmem => ?_⟩
  · rw [← hγq, ← hu, negInv_negInv']
  · obtain ⟨_, ⟨t, ht, rfl⟩, hvt⟩ := hmem
    rcases eq_or_lt_of_le hv.1 with hv0 | hv0
    · rw [← hv0, hη0] at hvt
      have : γ t = 0 := by
        have h2 := congrArg negInv hvt
        rw [negInv_negInv'] at h2
        simpa [negInv] using h2
      exact hγ0 t ht.1 this
    · refine hbefore v ⟨hv0, hv.2⟩ ⟨t, ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩, ?_⟩
      rw [← hvt, negInv_negInv']
      simp only [Sec7.Lemma71I.realPath, Real.toNNReal_coe]

/-- The counterflow read on `ℝ` through `toNNReal` agrees with a version on `ℝ` at positive times. -/
theorem counterflow_toNNReal_eq {η : ℝ → ℂ} (u : ℝ) (hu : 0 < u) :
    (fun s : ℝ => (fun t : ℝ≥0 => η t) s.toNNReal) u = η u := by
  simp only [Real.coe_toNNReal _ hu.le]

/-! ### The strip frame: heights and the first piece -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The (4.4) heights at every angle of `[−π/2, π/2]` from Aux. 130's height choice. -/
theorem heights_of_cum (hκ : 0 < κ) (hκ4 : κ < 4)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) : IsHeightBounded44 κ b J θ := by
  have hχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  exact ⟨fun y hy hyJ => by linarith [hleft θ hθ y hy hyJ], fun y hy hyJ => hright θ hθ y hy hyJ⟩

/-- **The first piece of a two-angle wall as a flow line**: the seed line of the first piece's driver is a version
of the angle-`θ₀` flow line of `h` (frozen `IsFlowLine`), almost surely of infinite lifetime, with a continuous
driver from `0`. -/
theorem firstPiece_isFlowLine (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
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
    hS.staged _ (Sec7.StripSys.isBoundaryContinuedProgram_twoAngleProg hθ₀ hθ t₀)
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

/-- **Before the switch a two-angle wall is its first piece**: almost surely a version of the wall agrees with the
seed line of the first piece on `[0, t₀]` (both generate the first piece's driver there). -/
theorem ae_eq_firstPiece_of_le (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {R : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ t₀ → R ω t = WangWu.seedLine (fun ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).2)
      (fun t ω => (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1 t) ω t := by
  filter_upwards [(firstPiece_isFlowLine hS hleft hright hθ₀ hθ t₀).2, hR.ae_isGeneratingTrace]
    with ω ⟨_, hw0, hc, hγ⟩ hRω t ht
  have hR' := IsGeneratingTrace.of_eqOn_lt hRω (T := (t₀ : ℝ≥0∞))
    (w := (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).1) fun s hs =>
      (catPath_of_le (ENNReal.coe_lt_coe.1 hs).le).symm
  exact IsGeneratingTrace.eq_of_le hR' (LP.isGeneratingTrace_mono hγ le_top) hc.continuousOn hw0
    (ENNReal.coe_le_coe.2 ht)

/-- A counterflow version on `ℝ`, read through `toNNReal`, has the same first contacts. -/
theorem isFirstHitQ_real_of_toNNReal {γ : ℝ → ℂ} {η : ℝ → ℂ} {q : ℝ} (hq : 0 < q)
    (h : IsFirstHitQ γ (fun s : ℝ => η (s.toNNReal : ℝ)) q) : IsFirstHitQ γ η q :=
  isFirstHitQ_congr hq (fun _ _ => rfl) (fun u hu => by simp only [Real.coe_toNNReal _ hu.le]) h

/-- **The one-angle law before the switch of a two-angle wall** (`q ≤ t₀`): the wall is its first piece there, the
angle-`θ₀` flow line of `h`, and Lemma 4.7 at relative angle `θ₀` applies (`ae_isFirstHitQ_of_isFlowLine_heights`). -/
theorem ae_isFirstHitQ_twoAngle_le {θ₀ θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ₀)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {R : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q)
    (hqt : (q : ℝ) ≤ t₀) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hfl := (firstPiece_isFlowLine hS hleft hright hθ₀ hθ t₀).1
  have hπ := heights_of_cum hκ hκ4 hleft hright Sec7.StripSys.pi_div_two_mem_Icc
  filter_upwards [ae_isFirstHitQ_of_isFlowLine_heights h47 href hκ hκ4 hS.boundaryData
      (heights_of_cum hκ hκ4 hleft hright hθ₀) hπ hS.gff hS.counterflow hS.lifetime hη hfl q hq,
    ae_eq_firstPiece_of_le hS hleft hright hθ₀ hθ hR] with ω h1 h2
  refine isFirstHitQ_congr (by exact_mod_cast hq) (fun s hs => ?_) (fun u _ => rfl) h1
  simp only [Sec7.Lemma71I.realPath]
  exact (h2 _ ((Real.toNNReal_le_iff_le_coe).2 (hs.2.trans hqt))).symm

/-- **The general restart law for the walls, after the switch** (named input; specification Lemma 5.7, p. 138, with
`ℓ = 2`, Figure 5.5 right panel, and Remark 5.8 (c); Aux. lemma 130, pp. 410–412). For every strip system with Aux.
130's height choice, every two-angle wall `η^{t₀,∞}_{θ₀,θ}` (angles in `[−π/2, π/2]`) with a version `R`, and every
continuous generating trace `η` of the counterflow driver: at every rational own time `q > t₀` after the switch,
almost surely the counterflow `R ∘ η` first contacts `R((0, q])` at `R(q)`. Mathematically: given the angle-varying
prefix `R([0, q])`, the counterflow mapped to the remaining domain is the counterflow of the conditional field, whose
data satisfy Lemma 4.5's heights, so it exits at the tip. Before the switch the law is proved
(`ae_isFirstHitQ_twoAngle_le`). -/
def SwitchedWallFirstHitStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) →
    ∀ θ₀ θ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → θ ∈ Icc (-(π / 2)) (π / 2) →
    ∀ (t₀ : ℝ≥0) (R : Ω → ℝ≥0 → ℂ),
      Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∀ q : ℚ, (t₀ : ℝ) < q →
      ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q

/-- **The restart law at every rational time of a two-angle wall**: before the switch from Lemma 4.7 at relative
angle `θ₀`, after it from the general law. -/
theorem ae_isFirstHitQ_twoAngle {θ₀ θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ₀)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : SwitchedWallFirstHitStatement.{u})
    (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {R : Ω → ℝ≥0 → ℂ} (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  rcases le_or_gt (q : ℝ) t₀ with hqt | hqt
  · exact ae_isFirstHitQ_twoAngle_le h47 href hS hleft hright hθ₀ hθ hR hη q hq hqt
  · exact hsw κ b J P h W' ζ' E hS hleft hright θ₀ θ hθ₀ hθ t₀ R hR η hη q hqt

/-- **The unchanged extremal wall `β = η_{π/2}`** (a one-angle wall: the left boundary of the counterflow): the
rational first-exit law from the landed Lemma 4.7 alone. -/
theorem ae_isFirstHitQ_leftExtremal (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
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
    filter_upwards [hβtr, Sec7.StripPocketPath.ae_simple_trace_leftExtremal_strip hS hleft hright]
      with ω htr hreg
    simpa only [hreg.1, Complex.ofReal_zero, sub_zero] using htr
  exact ae_isFirstHitQ_of_isFlowLine_pi_div_two h47 href hκ hκ4 hS.boundaryData
    (heights_of_cum hκ hκ4 hleft hright Sec7.StripSys.pi_div_two_mem_Icc) hS.gff hS.counterflow hS.lifetime hη hβ q hq

/-- **A constant-angle wall `η_θ`** (`R7Aux131.constSpec θ`, the walls of R.7): the rational first-exit law from
Lemma 4.7 at relative angle `θ`. -/
theorem ae_isFirstHitQ_const {θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2))
    (hreg : ∀ ω, Exist.Staged.IsRegularDriver (E (Sec7.R7Aux131.constSpec θ) 0 ω)) {γ : Ω → ℝ≥0 → ℂ}
    (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0)
    (hγtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (Sec7.R7Aux131.constSpec θ) 0 ω).1 ⊤ (γ ω))
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (γ ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have htr := Sec7.Aux37Walls.ae_trace_const hS hleft hright hθ hreg hγc hγ0 hγtr
  have hfl : IsFlowLine κ b J 0 θ P h γ (fun ω => (E (Sec7.R7Aux131.constSpec θ) 0 ω).2) := by
    refine Sec7.Aux37Walls.isFlowLine_const hS hθ ?_
    filter_upwards [htr] with ω hω
    rw [hω.1]
    exact hω.2.1
  exact ae_isFirstHitQ_of_isFlowLine_heights h47 href hκ hκ4 hS.boundaryData
    (heights_of_cum hκ hκ4 hleft hright hθ) (heights_of_cum hκ hκ4 hleft hright Sec7.StripSys.pi_div_two_mem_Icc)
    hS.gff hS.counterflow hS.lifetime hη hfl q hq

end Strip

end InteractingSLE.Sec5.RestartGen
