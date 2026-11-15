/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7OuterFlow
import InteractingSLE.Spec.Sec7.Lemma613Geom
import InteractingSLE.Spec.Supplement.SB4SewSides

/-!
# Theorem R.7, part (a): the order of the incoming arms relative to the certified frontiers

Packet PROVE-R7-OUTER. Supplement §5.1 (`source/spec/p433-480.md` L962–L966, p. 471): "The available non-boundary
inputs are the complete simple extremal flow lines `β_R, β_L` of angles `−π/2, +π/2`, the global side confinement of
`η`, non-boundary flow order […] Write `E_R, E_L` for the open exterior Jordan sides of `β_R, β_L`. […] An incoming
right arm is either a contained strict-angle line, the certified right frontier, or a simple non-boundary line
`α_R ⊂ Ē_R`. The last alternative is called an outer right arm."

`E_R` is the open right side `rightSideOf (range β_R)` of `β_R` (the component of `ℍ ∖ β_R` whose boundary contains
`[0, ∞)`), and `E_L = leftSideOf (range β_L)`. The order comes from **non-boundary flow order** (Proposition 5.5 in
`ℍ`, `Lemma71H.Prop55HalfPlaneStatement`, a consequence of Propositions 4.11 and 5.1 in chart `Q`,
`Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q`; R48-safe): for `θ₁ < θ₂` the angle-`θ₂` line lies in
the closed left side of the angle-`θ₁` line.

* Deterministic: for seed-proper `α`, `β` from `0` with `β ⊆ closedLeftSide α`,
  `range α ⊆ rightSideOf (range β) ∪ range β ⊆ closure (rightSideOf (range β))` (duality,
  `Supp9B.range_subset_closedRightSide`) and `range β ⊆ leftSideOf (range α) ∪ range α ⊆ closure (leftSideOf …)`.
* **`ae_order_of_lt`**: the probabilistic order of two flow lines of the data of Figure 7.1 in all these forms.
* **`ae_r7_order`**: Theorem R.7's configuration — for an outer right arm (`θ_R < −π/2`)
  `α_R ⊂ E_R ∪ β_R ⊂ Ē_R`; for an outer left arm (`θ_L > π/2`) `α_L ⊂ E_L ∪ β_L ⊂ Ē_L`; and `β_L` is in the closed
  left side of `β_R`.
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

variable {α β : ℝ≥0 → ℂ}

/-! ### Deterministic side conversions -/

theorem IsSeedProper.isProperCurve (h : IsSeedProper α) : Supp9B.IsProperCurve α :=
  ⟨h.1, h.2.1, Sec5.Prop55Half.IsSeedProper.im_nonneg h, h.2.2.2.2⟩

theorem IsSeedProper.isSimpleProper (h : IsSeedProper α) : Lemma71I.IsSimpleProper α := h

/-- A seed-proper curve is in the closure of its own right side. -/
theorem range_subset_closure_rightSideOf_self (hα : IsSeedProper α) :
    range α ⊆ closure (rightSideOf (range α)) := by
  rintro _ ⟨s, rfl⟩
  exact Lemma613.mem_closure_rightSideOf (IsSeedProper.isSimpleProper hα) s

/-- A seed-proper curve is in the closure of its own left side. -/
theorem range_subset_closure_leftSideOf_self (hα : IsSeedProper α) :
    range α ⊆ closure (leftSideOf (range α)) := by
  have hA := (IsSeedProper.isSimpleProper hα).isProperArc
  have hpos : ∀ s : ℝ≥0, 0 < s → α s ∈ closure (leftSideOf (range α)) := fun s hs => by
    have h := WangWu.IsProperArc.mem_closure_leftSideOf hA (s := (s : ℝ)) (by exact_mod_cast hs)
    rwa [Lemma71I.realPath_coe, Lemma71I.arcRange_realPath] at h
  rintro _ ⟨s, rfl⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
  · rw [← hs]
    have ht : Tendsto α (𝓝[>] 0) (𝓝 (α 0)) := (hα.1.tendsto 0).mono_left nhdsWithin_le_nhds
    exact isClosed_closure.mem_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => hpos s hs)
  · exact hpos s hs

/-- **Duality in the frozen sides** (deterministic): if `β` lies in the closed left side of `α` (both seed-proper from
`0`), then `α` lies in the closed right side `rightSideOf (range β) ∪ range β` of `β`. -/
theorem range_subset_rightSideOf_union (hα : IsSeedProper α) (hβ : IsSeedProper β)
    (hord : range β ⊆ closedLeftSide α) : range α ⊆ rightSideOf (range β) ∪ range β := by
  have hα0 : α 0 = 0 := hα.2.2.1
  have hβ0 : β 0 = 0 := hβ.2.2.1
  have hR := Supp9B.range_subset_closedRightSide (IsSeedProper.isProperCurve hα) (IsSeedProper.isProperCurve hβ)
    (by rw [hα0]; rfl) (by rw [hβ0]; rfl) (by rw [hα0, hβ0]) hord
  rintro _ ⟨t, rfl⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · exact Or.inr ⟨0, by rw [← ht, hα0, hβ0]⟩
  have hH : α t ∈ H := hα.2.2.2.1 t ht
  rcases hR ⟨t, rfl⟩ with hr | hs
  · exact Or.inl (Theorem14.SB.rightSide_inter_H_subset_rightSideOf (IsSeedProper.isProperCurve hβ) hβ0 ⟨hr, hH⟩)
  · rcases hs with hs | ⟨-, him⟩
    · exact Or.inr hs
    · exfalso
      rw [hβ0] at him
      have : 0 < (α t).im := hH
      simp only [Complex.zero_im] at him
      linarith

/-- If `β` lies in the closed left side of `α` (both seed-proper from `0`), then
`β ⊆ leftSideOf (range α) ∪ range α`. -/
theorem range_subset_leftSideOf_union (hα : IsSeedProper α) (hβ : IsSeedProper β)
    (hord : range β ⊆ closedLeftSide α) : range β ⊆ leftSideOf (range α) ∪ range α := by
  have hα0 : α 0 = 0 := hα.2.2.1
  have hβ0 : β 0 = 0 := hβ.2.2.1
  rintro _ ⟨t, rfl⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · exact Or.inr ⟨0, by rw [← ht, hα0, hβ0]⟩
  have hH : β t ∈ H := hβ.2.2.2.1 t ht
  rcases hord ⟨t, rfl⟩ with hl | hs
  · exact Or.inl (Theorem14.SB.leftSide_inter_H_subset_leftSideOf (IsSeedProper.isProperCurve hα) hα0 ⟨hl, hH⟩)
  · rcases hs with hs | ⟨-, him⟩
    · exact Or.inr hs
    · exfalso
      rw [hα0] at him
      have : 0 < (β t).im := hH
      simp only [Complex.zero_im] at him
      linarith

/-- `α ⊂ Ē` for the right side `E` of `β`. -/
theorem range_subset_closure_rightSideOf (hα : IsSeedProper α) (hβ : IsSeedProper β)
    (hord : range β ⊆ closedLeftSide α) : range α ⊆ closure (rightSideOf (range β)) := fun _ hz =>
  (range_subset_rightSideOf_union hα hβ hord hz).elim (fun h => subset_closure h)
    (fun h => range_subset_closure_rightSideOf_self hβ h)

/-- `β ⊂ Ē` for the left side `E` of `α`. -/
theorem range_subset_closure_leftSideOf (hα : IsSeedProper α) (hβ : IsSeedProper β)
    (hord : range β ⊆ closedLeftSide α) : range β ⊆ closure (leftSideOf (range α)) := fun _ hz =>
  (range_subset_leftSideOf_union hα hβ hord hz).elim (fun h => subset_closure h)
    (fun h => range_subset_closure_leftSideOf_self hα h)

/-! ### Non-boundary flow order -/

variable {κ : ℝ} {a b : ℝ}

/-- **Non-boundary flow order for the data of Figure 7.1** (Proposition 5.5 in `ℍ`): for `θ₁ < θ₂` with the (4.4)
bounds `b ≥ λ − θ₁χ` and `a ≥ λ − πχ + θ₂χ` (so both lines are non-boundary), almost surely both flow lines are
seed-proper with infinite lifetime, `η₂` lies in the closed left side of `η₁`, `η₁ ⊂ rightSideOf η₂ ∪ η₂` and
`η₂ ⊂ leftSideOf η₁ ∪ η₁`. -/
theorem ae_order_of_lt (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ}
    (hθ : θ₁ < θ₂) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ))
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (h₁ : IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁)
    (h₂ : IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ζ₁ ω = ⊤ ∧ ζ₂ ω = ⊤ ∧ IsSeedProper (η₁ ω) ∧ IsSeedProper (η₂ ω) ∧
      range (η₂ ω) ⊆ closedLeftSide (η₁ ω) ∧ range (η₁ ω) ⊆ rightSideOf (range (η₂ ω)) ∪ range (η₂ ω) ∧
      range (η₂ ω) ⊆ leftSideOf (range (η₁ ω)) ∪ range (η₁ ω) := by
  have hpc := isPiecewiseConstant_prop74Data a b
  have hH₁ := isHeightBounded44_prop74Data_of_mem_Icc hκ hκ4 ha hb ⟨le_rfl, hθ.le⟩
  have hH₂ := isHeightBounded44_prop74Data_of_mem_Icc hκ hκ4 ha hb ⟨hθ.le, le_rfl⟩
  filter_upwards [h55 κ hκ hκ4 a b θ₁ θ₂ hθ hb ha P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    IsFlowLine.ae_regular_of_heights hκ hκ4 hpc hH₁ h₁, IsFlowLine.ae_regular_of_heights hκ hκ4 hpc hH₂ h₂]
    with ω hord hr₁ hr₂
  have hord' := hord hr₁.1 hr₂.1
  exact ⟨hr₁.1, hr₂.1, hr₁.2, hr₂.2, hord', range_subset_rightSideOf_union hr₁.2 hr₂.2 hord',
    range_subset_leftSideOf_union hr₁.2 hr₂.2 hord'⟩

/-! ### Theorem R.7's configuration -/

/-- **The order of Theorem R.7's incoming arms and certified frontiers** (supplement §5.1, p. 471), for the field
with the R.7 data `−(r7A + c)` on `ℝ₋`, `r7B + c'` on `ℝ₊` (`c, c' ≥ 0`), flow parameter `κ = 16/k`: almost surely

* the four lines `α_R` (angle `θ_R`), `β_R` (`−π/2`), `β_L` (`π/2`), `α_L` (`θ_L`) are seed-proper with infinite
  lifetime;
* `β_L` lies in the closed left side of `β_R`;
* an **outer right arm** (`θ_R < −π/2`, i.e. `r_L > d`) satisfies `α_R ⊂ E_R ∪ β_R ⊂ Ē_R`, `E_R = rightSideOf β_R`;
* an **outer left arm** (`θ_L > π/2`, i.e. `r_R > d`) satisfies `α_L ⊂ E_L ∪ β_L ⊂ Ē_L`, `E_L = leftSideOf β_L`. -/
theorem ae_r7_order (h55 : Lemma71H.Prop55HalfPlaneStatement.{u}) {k rL rR : ℝ} (hk4 : 4 < k) (hL : -2 < rL)
    (hR : -2 < rR) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
    (hαR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaR k rL) P h αR ζαR)
    (hβR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (-(π / 2)) P h βR ζβR)
    (hβL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (π / 2) P h βL ζβL)
    (hαL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaL k rR) P h αL ζαL) :
    ∀ᵐ ω ∂P, IsSeedProper (αR ω) ∧ IsSeedProper (βR ω) ∧ IsSeedProper (βL ω) ∧ IsSeedProper (αL ω) ∧
      ζαR ω = ⊤ ∧ ζβR ω = ⊤ ∧ ζβL ω = ⊤ ∧ ζαL ω = ⊤ ∧
      range (βL ω) ⊆ closedLeftSide (βR ω) ∧
      (R7.thetaR k rL < -(π / 2) → range (αR ω) ⊆ rightSideOf (range (βR ω)) ∪ range (βR ω) ∧
        range (αR ω) ⊆ closure (rightSideOf (range (βR ω)))) ∧
      (π / 2 < R7.thetaL k rR → range (αL ω) ⊆ leftSideOf (range (βL ω)) ∪ range (βL ω) ∧
        range (αL ω) ⊆ closure (leftSideOf (range (βL ω)))) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hpc := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hb : ∀ θ, θ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR) → sleLambda (16 / k) - θ * chiC (16 / k) ≤
      r7B k rL + c' := fun θ hθ => by
    have hχ := Sec4.chiC_pos hκ hκ4
    have := mul_le_mul_of_nonneg_right hθ.1 hχ.le
    simp only [r7B]; linarith
  have ha : ∀ θ, θ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR) →
      sleLambda (16 / k) - π * chiC (16 / k) + θ * chiC (16 / k) ≤ r7A k rR + c := fun θ hθ => by
    have hχ := Sec4.chiC_pos hκ hκ4
    have := mul_le_mul_of_nonneg_right hθ.2 hχ.le
    simp only [r7A]; linarith
  have mR := thetaR_mem_r7 rR hk4 hL
  have mL := thetaL_mem_r7 rL hk4 hR
  have m1 := neg_pi_div_two_mem_r7 k rL rR
  have m2 := pi_div_two_mem_r7 k rL rR
  have hreg : ∀ {θ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}, θ ∈ Icc (r7ThetaLo k rL) (r7ThetaHi k rR) →
      IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 θ P h η ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsSeedProper (η ω) := fun hθ hfl =>
    IsFlowLine.ae_regular_of_heights hκ hκ4 hpc (isHeightBounded44_r7 hk4 hc hc' hθ) hfl
  have hext : ∀ᵐ ω ∂P, range (βL ω) ⊆ closedLeftSide (βR ω) := by
    filter_upwards [ae_order_of_lt h55 hκ hκ4 (by linarith [Real.pi_pos]) (hb _ m1) (ha _ m2) hh hβR hβL]
      with ω hω
    exact hω.2.2.2.2.1
  have hRo : R7.thetaR k rL < -(π / 2) → ∀ᵐ ω ∂P, range (αR ω) ⊆ rightSideOf (range (βR ω)) ∪ range (βR ω) ∧
      range (αR ω) ⊆ closure (rightSideOf (range (βR ω))) := fun hθ => by
    filter_upwards [ae_order_of_lt h55 hκ hκ4 hθ (hb _ mR) (ha _ m1) hh hαR hβR] with ω hω
    exact ⟨hω.2.2.2.2.2.1, range_subset_closure_rightSideOf hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2.1⟩
  have hLo : π / 2 < R7.thetaL k rR → ∀ᵐ ω ∂P, range (αL ω) ⊆ leftSideOf (range (βL ω)) ∪ range (βL ω) ∧
      range (αL ω) ⊆ closure (leftSideOf (range (βL ω))) := fun hθ => by
    filter_upwards [ae_order_of_lt h55 hκ hκ4 hθ (hb _ m2) (ha _ mL) hh hβL hαL] with ω hω
    exact ⟨hω.2.2.2.2.2.2, range_subset_closure_leftSideOf hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2.1⟩
  have hRo' : ∀ᵐ ω ∂P, R7.thetaR k rL < -(π / 2) → range (αR ω) ⊆ rightSideOf (range (βR ω)) ∪ range (βR ω) ∧
      range (αR ω) ⊆ closure (rightSideOf (range (βR ω))) := by
    by_cases hθ : R7.thetaR k rL < -(π / 2)
    · filter_upwards [hRo hθ] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h' => absurd h' hθ
  have hLo' : ∀ᵐ ω ∂P, π / 2 < R7.thetaL k rR → range (αL ω) ⊆ leftSideOf (range (βL ω)) ∪ range (βL ω) ∧
      range (αL ω) ⊆ closure (leftSideOf (range (βL ω))) := by
    by_cases hθ : π / 2 < R7.thetaL k rR
    · filter_upwards [hLo hθ] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h' => absurd h' hθ
  filter_upwards [hreg mR hαR, hreg m1 hβR, hreg m2 hβL, hreg mL hαL, hext, hRo', hLo'] with ω h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1.2, h2.2, h3.2, h4.2, h1.1, h2.1, h3.1, h4.1, h5, h6, h7⟩

end InteractingSLE.Sec7.R7Outer
