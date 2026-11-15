/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartGenConsumers
import InteractingSLE.Spec.Sec7.R7OuterReflect

/-!
# The restart law at relative angle `−π/2` by reflection

Packet PROVE-RESTART-GEN. The angle-`(−π/2)` flow line of `h` is the right boundary of the counterflow; under the
reflection `σ(z) = −z̄` it becomes the angle-`π/2` flow line (the left boundary) of the reflected field `−h ∘ σ`, whose
centred counterflow is driven by `−W′` (`R7Outer.isCenteredCounterflowDriver_reflect`,
`FlowReflect.IsFlowLine.reflect`). Lemma 4.7's first contact is invariant under `σ` (`σ` commutes with `R(z) = −1/z`
and is injective). Hence the one-angle restart law at `−π/2` follows from the landed Lemma 4.7 (relative angle
`π/2`) — no separate input:

* `isFirstHitQ_reflect`, `isHeightBounded44_reflData_of_cum`;
* **`ae_isFirstHitQ_of_isFlowLine_neg_pi_div_two`**: the one-angle law for the angle-`(−π/2)` flow line;
* `ae_isFirstHitQ_twoAngle_le_neg`, **`ae_isFirstHitQ_alpha`**: the wall `α = η^{1,∞}_{−π/2,θ₁}` before its switch from
  the landed Lemma 4.7, after it from `SwitchedWallFirstHitStatement`;
* **`hfirstR_of_restartGen'`**, **`hfirstα_path_of_restartGen'`**: the consumers' binders for `α` without the
  relative-angle-`(−π/2)` input.

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.RestartGen

open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec7.FlowReflect (reflData reflJumps reflField mem_reflJumps)
open Sec7.StripSideHeightProb (catPath)
open Exist.Staged (IsRegularDriver)
open LP (reflectC reflectC_reflectC)

/-- **Lemma 4.7's first contact is invariant under the reflection `σ(z) = −z̄`.** -/
theorem isFirstHitQ_reflect {γ β : ℝ → ℂ} {q : ℝ}
    (h : IsFirstHitQ (fun s => reflectC (γ s)) (fun s => reflectC (β s)) q) : IsFirstHitQ γ β q := by
  obtain ⟨u, hu0, hu, hbefore⟩ := h
  refine ⟨u, hu0, ?_, fun v hv hmem => hbefore v hv ?_⟩
  · have e := congrArg reflectC hu
    rwa [Sec7.R7Outer.negInv_reflectC, reflectC_reflectC, reflectC_reflectC] at e
  · obtain ⟨s, hs, e⟩ := hmem
    exact ⟨s, hs, by simp only [e, Sec7.R7Outer.negInv_reflectC]⟩

/-- The (4.4) heights at `π/2` of the reflected data `y ↦ −b(−y)` from Aux. 130's height choice at the angle `−π/2`. -/
theorem isHeightBounded44_reflData_of_cum {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) :
    IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2) := by
  have hχ : 0 ≤ chiC κ := (Sec4.chiC_pos hκ hκ4).le
  refine ⟨fun y hy hyJ => ?_, fun y hy hyJ => ?_⟩
  · have hyJ' : -y ∉ J := fun h => hyJ (mem_reflJumps.2 h)
    have := hright _ Sec7.StripSys.neg_pi_div_two_mem_Icc (-y) (by linarith) hyJ'
    simp only [reflData]
    nlinarith [Real.pi_pos]
  · have hyJ' : -y ∉ J := fun h => hyJ (mem_reflJumps.2 h)
    have := hleft _ Sec7.StripSys.neg_pi_div_two_mem_Icc (-y) (by linarith) hyJ'
    simp only [reflData]
    nlinarith [Real.pi_pos]

/-- **The one-angle restart law at relative angle `−π/2`** (the right boundary of the counterflow), from the landed
Lemma 4.7 by reflection: if the reflected data have (4.4) heights at `π/2`, `W′` drives the centred counterflow of
`h` with infinite lifetime and trace `η`, and `β` is the angle-`(−π/2)` flow line of `h`, then almost surely the
counterflow first contacts `β((0, q])` at `β(q)`. -/
theorem ae_isFirstHitQ_of_isFlowLine_neg_pi_div_two (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hθ : IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 (-(π / 2)) P h β ζ) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (β ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hβ' := Sec7.FlowReflect.IsFlowLine.reflect hb hβ
  rw [neg_zero, neg_neg] at hβ'
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W') t ω) ⊤ (fun t => reflectC (η ω t)) :=
    hη.mono fun ω hω => LP.isGeneratingTrace_reflect hω
  filter_upwards [ae_isFirstHitQ_of_isFlowLine_pi_div_two h47 href hκ hκ4
    (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb) hθ
    (Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh) (Sec7.R7Outer.isCenteredCounterflowDriver_reflect hκ hcf)
    hζ' hη' hβ' q hq] with ω hω
  exact isFirstHitQ_reflect hω

/-! ### The wall `α` -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Before the switch of a wall with first angle `−π/2`**, from the landed Lemma 4.7 (by reflection). -/
theorem ae_isFirstHitQ_twoAngle_le_neg {θ : ℝ} (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0} {R : Ω → ℝ≥0 → ℂ}
    (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec (-(π / 2)) t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q)
    (hqt : (q : ℝ) ≤ t₀) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hfl := (firstPiece_isFlowLine hS hleft hright Sec7.StripSys.neg_pi_div_two_mem_Icc hθ t₀).1
  filter_upwards [ae_isFirstHitQ_of_isFlowLine_neg_pi_div_two h47 href hκ hκ4 hS.boundaryData
      (isHeightBounded44_reflData_of_cum hκ hκ4 hleft hright) hS.gff hS.counterflow hS.lifetime hη hfl q hq,
    ae_eq_firstPiece_of_le hS hleft hright Sec7.StripSys.neg_pi_div_two_mem_Icc hθ hR] with ω h1 h2
  refine isFirstHitQ_congr (by exact_mod_cast hq) (fun s hs => ?_) (fun u _ => rfl) h1
  simp only [Sec7.Lemma71I.realPath]
  exact (h2 _ ((Real.toNNReal_le_iff_le_coe).2 (hs.2.trans hqt))).symm

/-- **The restart law at every rational time of a wall with first angle `−π/2`**: the landed Lemma 4.7 before the
switch, the general law after it. -/
theorem ae_isFirstHitQ_alpha {θ : ℝ} (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : SwitchedWallFirstHitStatement.{u})
    (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0} {R : Ω → ℝ≥0 → ℂ}
    (hR : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.twoAngleSpec (-(π / 2)) t₀ θ)) t₀ R)
    {η : Ω → ℝ≥0 → ℂ} (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (R ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  rcases le_or_gt (q : ℝ) t₀ with hqt | hqt
  · exact ae_isFirstHitQ_twoAngle_le_neg h47 href hS hleft hright hθ hR hη q hq hqt
  · exact hsw κ b J P h W' ζ' E hS hleft hright (-(π / 2)) θ Sec7.StripSys.neg_pi_div_two_mem_Icc hθ t₀ R hR η hη q
      hqt

/-- **`hfirstR`** of `PocketWordIn.pocketWordEvolution_of_stripSystem_firstHit` from the landed Lemma 4.7 and the
switched law (no relative-angle-`(−π/2)` input). -/
theorem hfirstR_of_restartGen' (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hsw : SwitchedWallFirstHitStatement.{u})
    (hS : Sec7.StripSys.IsStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2)) {α : Ω → ℝ≥0 → ℂ}
    (hvα : Sec7.StripWall.IsWallVersion P (E (Sec7.StripSys.alphaSpec θ₁)) 1 α) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (α ω)) (η ω) q := by
  intro q hq
  filter_upwards [ae_isFirstHitQ_alpha (η := fun ω (t : ℝ≥0) => η ω t) h47 href hsw hS hleft hright
    (Ioo_subset_Icc_self hθ₁) hvα hηtr q hq] with ω hω
  exact isFirstHitQ_real_of_toNNReal (by exact_mod_cast hq) hω

/-- **`hfirstα`** of `WallsPath.pocketWordEvolution_of_stripSystem_path` from the landed Lemma 4.7 and the switched
law. -/
theorem hfirstα_path_of_restartGen' (h47 : Prop411Q.Lemma47QHitStatement.{u})
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
  filter_upwards [hfirstR_of_restartGen' h47 href hsw hS hleft hright hθ₁ hv hηtr q hq, hs, hηtr]
    with ω hω hsω hηω
  exact isFirstHitPoint_rt hq (ne_zero_of_isSimpleProper hsω) hηω.1 hω

end Strip

end InteractingSLE.Sec5.RestartGen
