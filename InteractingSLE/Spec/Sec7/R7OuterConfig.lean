/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7OuterReflect
import InteractingSLE.Spec.Sec7.StripSysBorel

/-!
# Theorem R.7, part (a): the assembled non-boundary configuration

Packet PROVE-R7-OUTER. Supplement §5.1 and the first paragraph of the proof of Theorem R.7
(`source/spec/p433-480.md` L956–L966, L1058–L1063, pp. 471 and 477). The configuration consumed by §§5.2–5.7
(packets (b)–(e) of `planning/handoffs/PROVE-R7POCKET.md` §5 item 4):

* one GFF `h` on `ℍ` with the R.7 data `−(r7A + c)` on `ℝ₋`, `r7B + c'` on `ℝ₊` ("Choose the original boundary values
  large enough to make these two complete flow lines and the original counterflow non-boundary"), `c, c' ≥ 0`
  free for further largeness requirements;
* its centred counterflow `W′` (frozen `IsCenteredCounterflowDriver`, parameter `k > 4`, flow parameter `κ = 16/k`);
* the four incoming lines from the common seed `0`, each a flow line of `h` and a Borel function of the field at every
  sample: the right arm `α_R` (angle `θ_R`), the certified right frontier `β_R` (`−π/2`), the certified left frontier
  `β_L` (`π/2`), the left arm `α_L` (`θ_L`) — contained, extremal or **outer** according to `r_L, r_R` versus
  `d = k/2 − 4` (`R7.d_lt_rL_iff`, …);
* almost surely: all four are simple proper curves from `0`, in `ℍ` at positive times, with infinite lifetime;
  `β_L` is in the closed left side of `β_R` and `α_L` in the closed left side of `α_R`; an outer right arm lies in
  `E_R ∪ β_R ⊂ Ē_R`, an outer left arm in `E_L ∪ β_L ⊂ Ē_L`; a contained right arm lies in the closed left side of
  `β_R`, a contained left arm has `β_L` in its closed left side; and every trace of the counterflow avoids
  `E_R ∪ E_L` at every time.

`IsR7OuterConfig` records exactly these facts; **`exists_isR7OuterConfig`** constructs one on a standard Borel space
from Propositions 4.11 and 5.1 in chart `Q` (`Prop411QStatement`, `Prop51QStatement`; R48-safe inputs of Theorem 1.2's
chain); **`IsR7OuterConfig.of_field`** builds the four lines on **any** probability space already carrying the field
and the counterflow (for instance a strip system's, `Sec7.StripSys.IsStripSystem`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec7.R7Outer

open Sec5.Prop55Half (IsSeedProper)
open WangWu (negInv)

/-- **Theorem R.7's non-boundary configuration, part (a)** (see the module docstring), on a probability space: the
field `h` with the R.7 data, its centred counterflow `W′`, and the four incoming lines `α_R, β_R, β_L, α_L` with their
lifetimes. -/
structure IsR7OuterConfig (k rL rR c c' : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞) : Prop where
  gff : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ)
  counterflow : IsCenteredCounterflowDriver (16 / k) P h W' ζ'
  flow_αR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaR k rL) P h αR ζαR
  flow_βR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (-(π / 2)) P h βR ζβR
  flow_βL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (π / 2) P h βL ζβL
  flow_αL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaL k rR) P h αL ζαL
  borel : ∃ ΦαR ΦβR ΦβL ΦαL : DistOn upperHalfPlaneOpens → ℝ≥0 → ℂ, Measurable ΦαR ∧ Measurable ΦβR ∧
    Measurable ΦβL ∧ Measurable ΦαL ∧ ∀ ω, αR ω = ΦαR (h ω) ∧ βR ω = ΦβR (h ω) ∧ βL ω = ΦβL (h ω) ∧
      αL ω = ΦαL (h ω)
  regular : ∀ᵐ ω ∂P, IsSeedProper (αR ω) ∧ IsSeedProper (βR ω) ∧ IsSeedProper (βL ω) ∧ IsSeedProper (αL ω) ∧
    ζαR ω = ⊤ ∧ ζβR ω = ⊤ ∧ ζβL ω = ⊤ ∧ ζαL ω = ⊤
  order : ∀ᵐ ω ∂P, range (βL ω) ⊆ closedLeftSide (βR ω) ∧ range (αL ω) ⊆ closedLeftSide (αR ω) ∧
    (R7.thetaR k rL < -(π / 2) → range (αR ω) ⊆ rightSideOf (range (βR ω)) ∪ range (βR ω) ∧
      range (αR ω) ⊆ closure (rightSideOf (range (βR ω)))) ∧
    (π / 2 < R7.thetaL k rR → range (αL ω) ⊆ leftSideOf (range (βL ω)) ∪ range (βL ω) ∧
      range (αL ω) ⊆ closure (leftSideOf (range (βL ω)))) ∧
    (-(π / 2) < R7.thetaR k rL → range (αR ω) ⊆ closedLeftSide (βR ω)) ∧
    (R7.thetaL k rR < π / 2 → range (βL ω) ⊆ closedLeftSide (αL ω))
  avoid : ∀ᵐ ω ∂P, ζ' ω = ⊤ → ∀ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η' →
    ∀ t : ℝ≥0, negInv (η' t) ∉ rightSideOf (range (βR ω)) ∪ leftSideOf (range (βL ω))

/-- `ae_order_of_lt` for two angles of the R.7 range. -/
theorem ae_order_r7 (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c)
    (hc' : 0 ≤ c') {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) (h₁ : θ₁ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR))
    (h₂ : θ₂ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR)) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, range (η₂ ω) ⊆ closedLeftSide (η₁ ω) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hb : sleLambda (16 / k) - θ₁ * chiC (16 / k) ≤ r7B k rL + c' := by
    have := mul_le_mul_of_nonneg_right h₁.1 hχ.le
    simp only [r7B]; linarith
  have ha : sleLambda (16 / k) - π * chiC (16 / k) + θ₂ * chiC (16 / k) ≤ r7A k rR + c := by
    have := mul_le_mul_of_nonneg_right h₂.2 hχ.le
    simp only [r7A]; linarith
  filter_upwards [ae_order_of_lt h55 hκ hκ4 hθ hb ha hh hη₁ hη₂] with ω hω
  exact hω.2.2.2.2.1

/-- **The four lines on a given field** (Theorem R.7, first paragraph, as separate objects of the same field): on any
probability space carrying the GFF `h` with the R.7 data and a centred counterflow `W′` of `h`, the four incoming lines
exist as Borel functions of the field and form an `IsR7OuterConfig`. -/
theorem IsR7OuterConfig.of_field (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmax : k / 2 - 4 ≤ max rL rR) (hc : 0 ≤ c) (hc' : 0 ≤ c') {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ') :
    ∃ (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
      IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hpc := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have mR := thetaR_mem_r7 rR hk4 hL
  have mL := thetaL_mem_r7 rL hk4 hR
  have m1 := neg_pi_div_two_mem_r7 k rL rR
  have m2 := pi_div_two_mem_r7 k rL rR
  obtain ⟨ΦαR, ζαR, hΦαR, hαR, -, -⟩ :=
    exists_isFlowLine_borel_of_heights href hκ hκ4 hpc (isHeightBounded44_r7 hk4 hc hc' mR) hh
  obtain ⟨ΦβR, ζβR, hΦβR, hβR, -, -⟩ :=
    exists_isFlowLine_borel_of_heights href hκ hκ4 hpc (isHeightBounded44_r7 hk4 hc hc' m1) hh
  obtain ⟨ΦβL, ζβL, hΦβL, hβL, -, -⟩ :=
    exists_isFlowLine_borel_of_heights href hκ hκ4 hpc (isHeightBounded44_r7 hk4 hc hc' m2) hh
  obtain ⟨ΦαL, ζαL, hΦαL, hαL, -, -⟩ :=
    exists_isFlowLine_borel_of_heights href hκ hκ4 hpc (isHeightBounded44_r7 hk4 hc hc' mL) hh
  have hord := ae_r7_order h55 hk4 hL hR hc hc' hh hαR hβR hβL hαL
  have hRL := ae_order_r7 h55 hk4 hc hc' (R7.thetaR_lt_thetaL hk4 hL hR hmax) mR mL hh hαR hαL
  have hRc : ∀ᵐ ω ∂P, -(π / 2) < R7.thetaR k rL → range (fun t => (ΦαR (h ω)).2 t) ⊆
      closedLeftSide (fun t => (ΦβR (h ω)).2 t) := by
    by_cases hθ : -(π / 2) < R7.thetaR k rL
    · filter_upwards [ae_order_r7 h55 hk4 hc hc' hθ m1 mR hh hβR hαR] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h' => absurd h' hθ
  have hLc : ∀ᵐ ω ∂P, R7.thetaL k rR < π / 2 → range (fun t => (ΦβL (h ω)).2 t) ⊆
      closedLeftSide (fun t => (ΦαL (h ω)).2 t) := by
    by_cases hθ : R7.thetaL k rR < π / 2
    · filter_upwards [ae_order_r7 h55 hk4 hc hc' hθ mL m2 hh hαL hβL] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h' => absurd h' hθ
  refine ⟨_, _, _, _, ζαR, ζβR, ζβL, ζαL, ⟨hh, hcf, hαR, hβR, hβL, hαL,
    ⟨fun f => (ΦαR f).2, fun f => (ΦβR f).2, fun f => (ΦβL f).2, fun f => (ΦαL f).2,
      measurable_snd.comp hΦαR, measurable_snd.comp hΦβR, measurable_snd.comp hΦβL, measurable_snd.comp hΦαL,
      fun ω => ⟨rfl, rfl, rfl, rfl⟩⟩, ?_, ?_, ae_r7_counterflow_avoid h411 hk4 hc hc' hh hcf hβR hβL⟩⟩
  · filter_upwards [hord] with ω hω
    exact ⟨hω.1, hω.2.1, hω.2.2.1, hω.2.2.2.1, hω.2.2.2.2.1, hω.2.2.2.2.2.1, hω.2.2.2.2.2.2.1,
      hω.2.2.2.2.2.2.2.1⟩
  · filter_upwards [hord, hRL, hRc, hLc] with ω hω h1 h2 h3
    exact ⟨hω.2.2.2.2.2.2.2.2.1, h1, hω.2.2.2.2.2.2.2.2.2.1, hω.2.2.2.2.2.2.2.2.2.2, h2, h3⟩

/-- **Theorem R.7's non-boundary configuration exists** (part (a) of R.7's construction): for `k > 4`, weights
`r_L, r_R > −2` with `max(r_L, r_R) ≥ k/2 − 4` and any `c, c' ≥ 0`, on a standard Borel probability space there are
the GFF with the R.7 data, its centred counterflow and the four incoming lines with all the properties of
`IsR7OuterConfig`. Inputs: Propositions 4.11 and 5.1 in chart `Q` (R48-safe). -/
theorem exists_isR7OuterConfig (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) {k rL rR c c' : ℝ} (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmax : k / 2 - 4 ≤ max rL rR) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
      (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
      IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  obtain ⟨Ω, mΩ, hSB, P, hP, h, W', ζ', hh, hcf, -⟩ :=
    StripSysBorel.exists_isCenteredCounterflowDriver_standardBorel.{u} hκ
      (isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c'))
  obtain ⟨αR, βR, βL, αL, ζαR, ζβR, ζβL, ζαL, hcfg⟩ :=
    IsR7OuterConfig.of_field h411 h51 hk4 hL hR hmax hc hc' hh hcf
  exact ⟨Ω, mΩ, hSB, P, hP, h, W', ζ', αR, βR, βL, αL, ζαR, ζβR, ζβL, ζαL, hcfg⟩

end InteractingSLE.Sec7.R7Outer
