/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartGenWalls
import InteractingSLE.Spec.Sec7.StripPocketConfigWalls

/-!
# The restart law in the exact form of its wall consumers

Packet PROVE-RESTART-GEN. The rational first-exit binders of the pocket-word and R.7 assemblies, derived from the
restart law of `RestartGenWalls`:

* `PocketWordIn.pocketWordEvolution_of_stripSystem_firstHit`: `hfirstR` (the wall `α = η^{1,∞}_{−π/2,θ₁}`),
  `hfirstE` (the unchanged extremal wall `β = η_{π/2}`, **no input beyond the landed Lemma 4.7**), `hfirstL` (the walls
  `β^{(r)} = η^{r,∞}_{π/2,θ₂}`): `hfirstR_of_restartGen`, `hfirstE_of_restartGen`, `hfirstL_of_restartGen`;
* `WallsPath.pocketWordEvolution_of_stripSystem_path` (`Sec4.IsFirstHitPoint` form): `hfirstα_path_of_restartGen`,
  `hfirstL_path_of_restartGen`;
* `WallsPath.r7PocketStopStatement_of_stripSystem_path_prop74` (constant-angle walls, both):
  `hfirstConst_path_of_restartGen` — a one-angle wall, so only Lemma 4.7 at its relative angle is needed.

Inputs: Lemma 4.7 at the relative angles used (`Lemma47QHitTStatement`; at `π/2` the landed
`Prop411Q.Lemma47QHitStatement`), the §4.2 reference (from `Prop411QStatement` in these assemblies,
`Cond44Ref.cond44ReferenceStatement_of_prop411Q`), and, for the two-angle walls after their switch, the general law
`SwitchedWallFirstHitStatement`. R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`
or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function Bornology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.RestartGen

open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.StripSideHeightProb (catPath)
open Exist.Staged (IsRegularDriver)

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-! ### Wall versions from the pathwise data of the `WallsPath` assemblies -/

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- A continuous measurable curve from `0` that is almost surely a simple proper generating trace of the concatenated
driver is a wall version. -/
theorem isWallVersion_of_simpleProper {E₀ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {t₀ : ℝ≥0} {γ : Ω → ℝ≥0 → ℂ}
    (hc : ∀ ω, Continuous (γ ω)) (h0 : ∀ ω, γ ω 0 = 0) (hm : ∀ t, Measurable fun ω => γ ω t)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E₀ 0 ω).1 t₀ (E₀ 1 ω).1) ⊤ (γ ω))
    (hs : ∀ᵐ ω ∂P, Sec7.Lemma71I.IsSimpleProper (γ ω)) : Sec7.StripWall.IsWallVersion P E₀ t₀ γ where
  continuous := hc
  zero := h0
  measurable := hm
  ae_trace := by
    filter_upwards [htr, hs] with ω h1 h2
    exact ⟨h1, h2.2.1, h2.2.2.2.1, tendsto_norm_atTop_iff_cobounded.1 h2.2.2.2.2⟩

/-- The time `rt q` read in `ℝ` is `q` (for `q > 0`). -/
theorem coe_rt {q : ℚ} (hq : 0 < q) : ((Sec7.StripSys.rt q : ℝ≥0) : ℝ) = q :=
  Real.coe_toNNReal _ (by exact_mod_cast hq.le)

/-- From `IsFirstHitQ` at a positive rational `q` to the `IsFirstHitPoint` form at `rt q`. -/
theorem isFirstHitPoint_rt {γ : ℝ≥0 → ℂ} {η : ℝ → ℂ} {q : ℚ} (hq : 0 < q) (hγ0 : ∀ t : ℝ≥0, 0 < t → γ t ≠ 0)
    (hη0 : η 0 = 0) (h : IsFirstHitQ (Sec7.Lemma71I.realPath γ) η q) :
    ∃ T : ℝ, Sec4.IsFirstHitPoint η T (negInv '' (γ '' Ioc 0 (Sec7.StripSys.rt q)))
      (negInv (γ (Sec7.StripSys.rt q))) := by
  refine isFirstHitPoint_of_isFirstHitQ (Real.toNNReal_pos.2 (by exact_mod_cast hq)) hγ0 hη0 ?_
  rw [coe_rt hq]
  exact h

/-- A simple proper wall is nonzero at positive times. -/
theorem ne_zero_of_isSimpleProper {γ : ℝ≥0 → ℂ} (hγ : Sec7.Lemma71I.IsSimpleProper γ) (t : ℝ≥0) (ht : 0 < t) :
    γ t ≠ 0 := by
  intro h0
  have hH := hγ.2.2.2.1 t ht
  rw [h0] at hH
  exact absurd hH (by simp [H])

/-! ### The binders of `PocketWordIn.pocketWordEvolution_of_stripSystem_firstHit` -/

/-- **`hfirstR`** (the wall `α = η^{1,∞}_{−π/2,θ₁}`): Lemma 4.7 at relative angle `−π/2` before the switch at own
time `1`, the general law after it. -/
theorem hfirstR_of_restartGen (h47m : Lemma47QHitTStatement.{u} (-(π / 2)))
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : SwitchedWallFirstHitStatement.{u})
    (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) {α : Ω → ℝ≥0 → ℂ}
    (hvα : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.alphaSpec θ₁)) 1 α) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (α ω)) (η ω) q := by
  intro q hq
  filter_upwards [ae_isFirstHitQ_twoAngle (η := fun ω (t : ℝ≥0) => η ω t) h47m href hsw hS hleft hright
    Sec7.StripSys.neg_pi_div_two_mem_Icc (Ioo_subset_Icc_self hθ₁) hvα hηtr q hq] with ω hω
  exact isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω

/-- **`hfirstE`** (the unchanged extremal wall `β = η_{π/2}`): from the landed Lemma 4.7 alone. -/
theorem hfirstE_of_restartGen (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {β : Ω → ℝ≥0 → ℂ} (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E Sec7.StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (β ω)) (η ω) q := by
  intro q hq
  filter_upwards [ae_isFirstHitQ_leftExtremal (η := fun ω (t : ℝ≥0) => η ω t) h47 href hS hleft hright hβtr hηtr
    q hq] with ω hω
  exact isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω

/-- **`hfirstL`** (the walls `β^{(r)} = η^{r,∞}_{π/2,θ₂}`): the landed Lemma 4.7 before the switch at own time `r`,
the general law after it. -/
theorem hfirstL_of_restartGen (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : SwitchedWallFirstHitStatement.{u})
    (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2)) {Lr : ℚ → Ω → ℝ≥0 → ℂ}
    (hvL : ∀ q, Sec7.StripWall.IsWallVersion P
      (E (Sec7.StripSys.betaSpec (Sec7.StripSys.rt (Sec7.PocketWordIn.positiveSeed q)) θ₂))
      (Sec7.StripSys.rt (Sec7.PocketWordIn.positiveSeed q)) (Lr q)) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ r : ℚ, 0 < r → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (Lr r ω)) (η ω) q := by
  intro r _ q hq
  filter_upwards [ae_isFirstHitQ_twoAngle (η := fun ω (t : ℝ≥0) => η ω t) (lemma47QHitTStatement_pi_div_two h47)
    href hsw hS hleft hright Sec7.StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθ₂) (hvL r) hηtr q hq]
    with ω hω
  exact isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω

/-! ### The binders of the `WallsPath` assemblies (`Sec4.IsFirstHitPoint` form) -/

/-- **`hfirstα`** of `WallsPath.pocketWordEvolution_of_stripSystem_path`, from its pathwise data. -/
theorem hfirstα_path_of_restartGen (h47m : Lemma47QHitTStatement.{u} (-(π / 2)))
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : SwitchedWallFirstHitStatement.{u})
    (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hregα : ∀ j ω, IsRegularDriver (E (Sec7.StripSys.alphaSpec θ₁) j ω)) {α : Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαtr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E (Sec7.StripSys.alphaSpec θ₁) 0 ω).1 1
      (E (Sec7.StripSys.alphaSpec θ₁) 1 ω).1) ⊤ (α ω))
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (α ω '' Ioc 0 (Sec7.StripSys.rt q)))
        (negInv (α ω (Sec7.StripSys.rt q))) := by
  have hs := Sec7.StripWall.ae_isSimpleProper_alpha hS hleft hright (Ioo_subset_Icc_self hθ₁) hregα hαc hα0 hαtr
  have hv := isWallVersion_of_simpleProper hαc hα0 hαm hαtr hs
  intro q hq
  filter_upwards [hfirstR_of_restartGen h47m href hsw hS hleft hright hθ₁ hv hηtr q hq, hs, hηtr]
    with ω hω hsω hηω
  exact isFirstHitPoint_rt hq (ne_zero_of_isSimpleProper hsω) hηω.1 hω

/-- **`hfirstL`** of `WallsPath.pocketWordEvolution_of_stripSystem_path`, from its pathwise data. -/
theorem hfirstL_path_of_restartGen (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : SwitchedWallFirstHitStatement.{u})
    (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₂ : ℝ} (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hregβ : ∀ q : ℚ, 0 < q → ∀ j ω, IsRegularDriver (E (Sec7.StripSys.betaSpec (Sec7.StripSys.rt q) θ₂) j ω))
    {Lr : ℚ → Ω → ℝ≥0 → ℂ} (hLc : ∀ q ω, Continuous (Lr q ω)) (hL0 : ∀ q ω, Lr q ω 0 = 0)
    (hLm : ∀ q t, Measurable fun ω => Lr q ω t)
    (hLtr : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsGeneratingTrace
      (catPath (E (Sec7.StripSys.betaSpec (Sec7.StripSys.rt q) θ₂) 0 ω).1 (Sec7.StripSys.rt q)
        (E (Sec7.StripSys.betaSpec (Sec7.StripSys.rt q) θ₂) 1 ω).1) ⊤ (Lr q ω))
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ r : ℚ, 0 < r → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (Lr r ω '' Ioc 0 (Sec7.StripSys.rt q)))
        (negInv (Lr r ω (Sec7.StripSys.rt q))) := by
  intro r hr q hq
  have hs := Sec7.StripWall.ae_isSimpleProper_beta hS hleft hright (Ioc_subset_Icc_self hθ₂) (Sec7.StripSys.rt r)
    (hregβ r hr) (hLc r) (hL0 r) (hLtr r hr)
  have hv := isWallVersion_of_simpleProper (hLc r) (hL0 r) (hLm r) (hLtr r hr) hs
  filter_upwards [ae_isFirstHitQ_twoAngle (η := fun ω (t : ℝ≥0) => η ω t) (lemma47QHitTStatement_pi_div_two h47)
    href hsw hS hleft hright Sec7.StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθ₂) hv hηtr q hq, hs, hηtr]
    with ω hω hsω hηω
  exact isFirstHitPoint_rt hq (ne_zero_of_isSimpleProper hsω) hηω.1
    (isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω)

/-- **`hfirstR`/`hfirstL` of R.7** (`WallsPath.r7PocketStopStatement_of_stripSystem_path_prop74`): a constant-angle
wall `η_θ` of the strip system; one-angle, so Lemma 4.7 at relative angle `θ` suffices. -/
theorem hfirstConst_path_of_restartGen {θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (hreg : ∀ ω, IsRegularDriver (E (Sec7.R7Aux131.constSpec θ) 0 ω))
    {R : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E (Sec7.R7Aux131.constSpec θ) 0 ω).1 ⊤ (R ω))
    {η : Ω → ℝ → ℂ} (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (Sec7.StripSys.rt q)))
        (negInv (R ω (Sec7.StripSys.rt q))) := by
  intro q hq
  filter_upwards [ae_isFirstHitQ_const (η := fun ω (t : ℝ≥0) => η ω t) h47 href hS hleft hright hθ hreg hRc hR0
    hRtr hηtr q hq, Sec7.Aux37Walls.ae_trace_const hS hleft hright hθ hreg hRc hR0 hRtr, hηtr]
    with ω hω htω hηω
  refine isFirstHitPoint_rt hq (fun t ht => ?_) hηω.1 (isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω)
  intro h0
  have hH := htω.2.2.2.1 t ht
  rw [h0] at hH
  exact absurd hH (by simp [H])

end InteractingSLE.Sec5.RestartGen
