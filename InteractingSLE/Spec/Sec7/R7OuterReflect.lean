/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7OuterAvoid
import InteractingSLE.Spec.Sec7.StripWallInputsRefl
import InteractingSLE.Spec.Sec7.StripSysField
import InteractingSLE.Spec.Coupling.MartMeans2Chart

/-!
# Theorem R.7, part (a): the counterflow avoids `E_R ∪ E_L` (the right side by reflection)

Packet PROVE-R7-OUTER. Supplement §5.1 (`source/spec/p433-480.md` L962–L964, p. 471): "Write `E_R, E_L` for the open
exterior Jordan sides of `β_R, β_L`. Then `η` avoids `E_R ∪ E_L` throughout its lifetime."

`R7OuterAvoid.lean` proves the left half from Proposition 4.11. The right half is its mirror image under the
reflection `σ(z) = −z̄`:

* **`isChartTransport_infinitySourceChart_reflect`**: the infinity-source chart transport of FD12 commutes with
  `σ` when the additive constant is `a = πk` (`R ∘ σ = σ ∘ R`; the lift `L(z) = −2 arg z` satisfies
  `L(σ z) = −L(z) − 2π` on `ℍ`, which is absorbed exactly by `a = πk`);
* **`isCenteredCounterflowDriver_reflect`**: if `W′` drives the centred counterflow of `h`, then `−W′` drives the
  centred counterflow of `−h ∘ σ` (here `a = −πχ = πχ(16/κ)` since `χ(16/κ) = −χ(κ)`);
* `reflectC_mem_leftSideOf_of_mem_rightSideOf`: `σ` maps the right side of `A` into the left side of `σ(A)`;
* **`ae_negInv_trace_notMem_rightSideOf`**: every trace of the counterflow avoids `E_R = rightSideOf β_R`, `β_R` the
  angle-`(−π/2)` flow line (from the left half for the reflected field, whose angle-`π/2` line is `σ ∘ β_R`);
* **`ae_negInv_trace_notMem_exteriors`**: both halves; **`ae_r7_counterflow_avoid`**: Theorem R.7's data.

R48: only `Prop411QStatement` and lemmas proved without Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real ComplexConjugate
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec7.R7Outer

open FlowReflect (reflField reflData reflJumps reflTest)
open LP (reflectC)
open WangWu (negInv)
open StripHeights44 (IsHeightBounded44)

/-! ### The reflection and the infinity-source chart -/

theorem negInv_reflectC (z : ℂ) : negInv (reflectC z) = reflectC (negInv z) := by
  simp [negInv, LP.reflectC, map_inv₀]

theorem negInv_image_H : (fun z : ℂ => -z⁻¹) '' H = H :=
  Subset.antisymm (fun _ ⟨_, hw, e⟩ => e ▸ StripSysField.negInv_mem_H hw) fun z hz =>
    ⟨-z⁻¹, StripSysField.negInv_mem_H hz, StripSysField.negInv_negInv z⟩

/-- The lift `L(z) = Im(−2 Log z) = −2 arg z` of the infinity-source chart under `σ`: `L(σ z) = −L(z) − 2π` on `ℍ`. -/
theorem lift_reflectC {z : ℂ} (hz : z ∈ H) :
    infinitySourceChart.2.2 (reflectC z) = -infinitySourceChart.2.2 z - 2 * π := by
  rw [StripSysField.infinitySourceChart_lift, StripSysField.infinitySourceChart_lift]
  have hz' : 0 < z.im := hz
  have him : (conj z).im < 0 := by simp only [Complex.conj_im]; linarith
  have harg : Complex.arg z ≠ π := (Complex.arg_lt_pi_iff.2 (Or.inr hz'.ne')).ne
  simp only [LP.reflectC]
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him, Complex.arg_conj]
  simp only [harg, ↓reduceIte]
  ring

/-- **The infinity-source chart transport commutes with the reflection** when `a = πk`. -/
theorem isChartTransport_infinitySourceChart_reflect {a k : ℝ} (hak : a = π * k)
    {h h' : DistOn upperHalfPlaneOpens} (hT : IsChartTransport infinitySourceChart (-1) a k h h') :
    IsChartTransport infinitySourceChart (-1) a k (reflField h) (reflField h') := by
  have hRH : infinitySourceChart.2.1 '' H = H := negInv_image_H
  intro φ φ' hsupp hφ
  rw [hRH] at hsupp
  have hsupp' : tsupport (reflTest φ) ⊆ infinitySourceChart.2.1 '' H := by
    rw [hRH, FlowReflect.tsupport_reflTest]
    rintro _ ⟨z, hz, rfl⟩
    exact LP.reflectC_mem_H_iff.2 (hsupp hz)
  have hrel : ∀ z ∈ infinitySourceChart.2.1 '' H,
      reflTest φ z = reflTest φ' (infinitySourceChart.1 z) * ‖deriv infinitySourceChart.1 z‖ ^ 2 := by
    intro z hz
    rw [hRH] at hz
    have hσz : reflectC z ∈ infinitySourceChart.2.1 '' H := by
      rw [hRH]; exact LP.reflectC_mem_H_iff.2 hz
    rw [FlowReflect.reflTest_apply, FlowReflect.reflTest_apply, hφ _ hσz]
    change φ' (-(reflectC z)⁻¹) * ‖deriv (fun z : ℂ => -z⁻¹) (reflectC z)‖ ^ 2 =
      φ' (reflectC (-z⁻¹)) * ‖deriv (fun z : ℂ => -z⁻¹) z‖ ^ 2
    rw [StripSysField.norm_deriv_negInv, StripSysField.norm_deriv_negInv, LP.norm_reflectC]
    congr 2
    exact negInv_reflectC z
  have key := hT (reflTest φ) (reflTest φ') hsupp' hrel
  have hφi : Integrable fun w => φ' w := φ'.continuous.integrable_of_hasCompactSupport φ'.hasCompactSupport
  have hcont : ContinuousOn (fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 w)) H :=
    StripSysField.continuousOn_infinitySourceChart_lift'.comp Chart.isConformal_infinitySourceChart.1.continuousOn
      fun z hz => StripSysField.negInv_mem_H hz
  have hi : Integrable fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn hcont φ' φ'.tsupport_subset
  have hI1 : ∫ w, reflTest φ' w = ∫ w, φ' w := FlowReflect.integral_comp_reflectC (fun w => φ' w)
  have hI2 : ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * reflTest φ' w =
      -(∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w) - 2 * π * ∫ w, φ' w := by
    have e1 : ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * reflTest φ' w =
        ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 (reflectC w)) * φ' w := by
      rw [← FlowReflect.integral_comp_reflectC
        (fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 (reflectC w)) * φ' w)]
      congr 1
      funext w
      simp only [LP.reflectC_reflectC, FlowReflect.reflTest_apply]
    have e2 : (fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 (reflectC w)) * φ' w) =
        fun w => -(infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w) - 2 * π * φ' w := by
      funext w
      by_cases hw : w ∈ H
      · have e : infinitySourceChart.2.1 (reflectC w) = reflectC (infinitySourceChart.2.1 w) := negInv_reflectC w
        rw [e, lift_reflectC (z := infinitySourceChart.2.1 w) (StripSysField.negInv_mem_H hw)]
        ring
      · have h0 : φ' w = 0 := φ'.zero_on_compl (show w ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hw)
        rw [h0]
        ring
    have hneg : Integrable fun w => -(infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ' w) := hi.neg
    rw [e1, e2, integral_sub hneg (hφi.const_mul _), integral_neg, integral_const_mul]
  rw [FlowReflect.reflField_apply, FlowReflect.reflField_apply, key, hI1, hI2, hak]
  ring

/-- **Reflection of the centred counterflow**: if `W` drives the centred counterflow of `h` (parameter `κ > 0`), then
`−W` drives the centred counterflow of `−h ∘ σ`, with the same lifetime. -/
theorem isCenteredCounterflowDriver_reflect {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) :
    IsCenteredCounterflowDriver κ P (fun ω => reflField (h ω)) (-W) ζ := by
  obtain ⟨b', J', h', hb', htr, hd⟩ := hcf
  have hak : -(π * chiC κ) = π * chiC (16 / κ) := by rw [Sec4.chiC_sixteen_div hκ]; ring
  refine ⟨reflData b', reflJumps J', fun ω => reflField (h' ω),
    FlowReflect.isPiecewiseConstantBoundaryData_reflData hb',
    fun ω => isChartTransport_infinitySourceChart_reflect hak (htr ω), ?_⟩
  have := StripWall.isFlowLineDriver_reflect hb' hd
  rwa [neg_zero] at this

/-- `σ` maps the right side of `A` into the left side of `σ(A)`. -/
theorem reflectC_mem_leftSideOf_of_mem_rightSideOf {A : Set ℂ} {z : ℂ} (hz : z ∈ rightSideOf A) :
    reflectC z ∈ leftSideOf (reflectC '' A) := by
  obtain ⟨⟨hzH, hzA⟩, x, hx, hxA, hxc⟩ := hz
  have hmemA : ∀ w : ℂ, reflectC w ∈ reflectC '' A → w ∈ A := fun w ⟨v, hv, e⟩ => by
    have := congrArg reflectC e
    rw [LP.reflectC_reflectC, LP.reflectC_reflectC] at this
    exact this ▸ hv
  have hrx : reflectC (x : ℂ) = ((-x : ℝ) : ℂ) := by simp [LP.reflectC]
  refine ⟨⟨LP.reflectC_mem_H_iff.2 hzH, fun h => hzA (hmemA z h)⟩, -x, by linarith, fun h => hxA (hmemA _ ?_), ?_⟩
  · rwa [hrx]
  · rw [LP.H_diff_reflectC_image, ← hrx, ← LP.coe_reflectHomeo,
      ← Homeomorph.image_connectedComponentIn (s := H \ A) LP.reflectHomeo (show z ∈ H \ A from ⟨hzH, hzA⟩),
      ← Homeomorph.image_closure]
    exact Set.mem_image_of_mem _ hxc


/-! ### The counterflow avoids `E_R` -/

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- **Every trace of the counterflow avoids `E_R` at every time** (supplement §5.1, right half). If the reflected
data `y ↦ −b(−y)` have (4.4) heights at `π/2` (equivalently: `b + (−π/2)χ ≤ −λ` left of `0` and
`b + (−π/2)χ ≥ λ − πχ` right of `0`), `W′` drives the centred counterflow of `h` and `β_R` is the angle-`(−π/2)` flow
line of `h`, then almost surely, on infinite lifetime, every continuous generating trace `γ′` of `W′` has
`R(γ′(t)) ∉ rightSideOf β_R` at every time. -/
theorem ae_negInv_trace_notMem_rightSideOf (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hθ : IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2)) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 (-(π / 2)) P h β ζ) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ → ∀ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η' →
      ∀ t : ℝ≥0, negInv (η' t) ∉ rightSideOf (range (β ω)) := by
  have hβ' := FlowReflect.IsFlowLine.reflect hb hβ
  rw [neg_zero, neg_neg] at hβ'
  have hL := ae_negInv_trace_notMem_leftSideOf h411 hκ hκ4 (FlowReflect.isPiecewiseConstantBoundaryData_reflData hb)
    hθ (FlowReflect.IsGFFWithBoundaryData.reflect hh) (isCenteredCounterflowDriver_reflect hκ hcf) hβ'
  filter_upwards [hL] with ω hω hζ η' hη t hmem
  have hη' : IsGeneratingTrace (fun t => (-W') t ω) ⊤ (fun t => reflectC (η' t)) :=
    LP.isGeneratingTrace_reflect hη
  refine hω hζ _ hη' t ?_
  have e : range (fun t => reflectC (β ω t)) = reflectC '' range (β ω) := (range_comp reflectC (β ω)).symm ▸ rfl
  rw [negInv_reflectC, e]
  exact reflectC_mem_leftSideOf_of_mem_rightSideOf hmem

/-- **The counterflow avoids `E_R ∪ E_L` throughout its lifetime** (supplement §5.1, p. 471): with (4.4) heights at
`π/2` for the data and for the reflected data, the centred counterflow `W′` of `h`, `β_R` (angle `−π/2`) and `β_L`
(angle `π/2`): almost surely `β_R`, `β_L` are seed-proper and, on infinite lifetime, every trace `γ′` of `W′` has
`R(γ′(t)) ∉ rightSideOf β_R ∪ leftSideOf β_L` at every time. -/
theorem ae_negInv_trace_notMem_exteriors (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J) (hθL : IsHeightBounded44 κ b J (π / 2))
    (hθR : IsHeightBounded44 κ (reflData b) (reflJumps J) (π / 2)) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') {βR βL : Ω → ℝ≥0 → ℂ} {ζR ζL : Ω → ℝ≥0∞}
    (hβR : IsFlowLine κ b J 0 (-(π / 2)) P h βR ζR) (hβL : IsFlowLine κ b J 0 (π / 2) P h βL ζL) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ → ∀ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η' →
      ∀ t : ℝ≥0, negInv (η' t) ∉ rightSideOf (range (βR ω)) ∪ leftSideOf (range (βL ω)) := by
  filter_upwards [ae_negInv_trace_notMem_rightSideOf h411 hκ hκ4 hb hθR hh hcf hβR,
    ae_negInv_trace_notMem_leftSideOf h411 hκ hκ4 hb hθL hh hcf hβL] with ω hR hL hζ η' hη t hmem
  rcases hmem with hm | hm
  · exact hR hζ η' hη t hm
  · exact hL hζ η' hη t hm

/-! ### Theorem R.7's data -/

/-- The reflected data of Figure 7.1 have (4.4) heights at `π/2` as soon as `a, b ≥ λ − (π/2)χ`. -/
theorem isHeightBounded44_refl_prop74Data {a b' : ℝ} (ha : sleLambda κ - π / 2 * chiC κ ≤ a)
    (hb' : sleLambda κ - π / 2 * chiC κ ≤ b') :
    IsHeightBounded44 κ (reflData (prop74Data a b')) (reflJumps {0}) (π / 2) := by
  refine ⟨fun y hy _ => ?_, fun y hy _ => ?_⟩
  · simp only [reflData, prop74Data, show ¬ (-y < 0) by linarith, ↓reduceIte]
    linarith
  · simp only [reflData, prop74Data, show -y < 0 by linarith, ↓reduceIte]
    linarith

/-- **Theorem R.7's counterflow avoids `E_R ∪ E_L`**, for the field with the R.7 data `−(r7A + c)` on `ℝ₋`,
`r7B + c'` on `ℝ₊` (`c, c' ≥ 0`), flow parameter `κ = 16/k`, counterflow parameter `k > 4`. -/
theorem ae_r7_counterflow_avoid (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) {k rL rR : ℝ} (hk4 : 4 < k)
    {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ')
    {βR βL : Ω → ℝ≥0 → ℂ} {ζR ζL : Ω → ℝ≥0∞}
    (hβR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (-(π / 2)) P h βR ζR)
    (hβL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (π / 2) P h βL ζL) :
    ∀ᵐ ω ∂P, ζ' ω = ⊤ → ∀ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ η' →
      ∀ t : ℝ≥0, negInv (η' t) ∉ rightSideOf (range (βR ω)) ∪ leftSideOf (range (βL ω)) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hpc := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hθL := isHeightBounded44_r7 (rL := rL) hk4 hc hc' (pi_div_two_mem_r7 k rL rR)
  have hlo : r7ThetaLo k rL ≤ -(π / 2) := min_le_right _ _
  have hhi : π / 2 ≤ r7ThetaHi k rR := le_max_right _ _
  have h1 := mul_le_mul_of_nonneg_right hlo hχ.le
  have h2 := mul_le_mul_of_nonneg_right hhi hχ.le
  have hθR : IsHeightBounded44 (16 / k) (reflData (prop74Data (r7A k rR + c) (r7B k rL + c'))) (reflJumps {0})
      (π / 2) := by
    refine isHeightBounded44_refl_prop74Data ?_ ?_
    · simp only [r7A]; nlinarith [Real.pi_pos]
    · simp only [r7B]; nlinarith [Real.pi_pos]
  exact ae_negInv_trace_notMem_exteriors h411 hκ hκ4 hpc hθL hθR hh hcf hβR hβL

end InteractingSLE.Sec7.R7Outer
