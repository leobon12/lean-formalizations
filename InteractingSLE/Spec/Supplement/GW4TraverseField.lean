/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowCode
import InteractingSLE.Spec.Supplement.GW2ConeData
import InteractingSLE.Spec.Supplement.GB6Contact
import InteractingSLE.Spec.Sec7.Aux122Disint
import InteractingSLE.Spec.Exist.Param12Canonical

/-!
# Theorem GW4: the canonical centred counterflow of a component field

Packet PROVE-T14-GW4T. Theorem GW4, proof (`source/spec/p625-671.md` L254–L260, pp. 638–639): "That lemma forces
`δ_s = 0` and identifies the canonical integrated finite-word system […] Universal determination makes each actual
complete component traversal a function of its own component field and its recorded initial finite word."

For a GFF `h_C` with piecewise-constant data `b_C` under any probability measure (in GW4: the conditional law `ν`
given the two walks), the frozen `IsCenteredCounterflowDriver` asks for a driver of the angle-`0` flow line at
`16/κ` of the inverted parameter field `F_d(h_C)^R = −h_C ∘ R + πχ − 2χ arg` (`R(z) = −1/z`). Here that driver is
written down explicitly as a Borel function of the field (Theorem 1.2 jointly measurable in the word, R44, and
Theorem 1.3), and its law is proved.

## Main definitions

* `cfField κ f`: the inverted parameter field, written as a return field (`Sec7.StripSysField.returnField`) with
  coefficients `(−πχ − 2πχ(16/κ), −χ(16/κ))`;
* `cfDrv h12p hκ bC jumpsC f`: the field-determined driver and lifetime of the counterflow word of `bC`
  (`Exist.Staged.drvOf ∘ detCode`, the realization used by `Restart.isOptionalHullCoupling_of_detAgree`).

## Main results

* `ae_ae_condExpKernel`: a `P`-almost sure property holds under almost every conditional law `condExpKernel P m ω₀`,
  for every σ-algebra `m` (not only `m ≤ mΩ`: Mathlib conditions on `m ⊓ mΩ`);
* `isChartTransport_cfField`: `cfField κ f` is the frozen infinity-source transport of `f`
  (coefficients `(−1, −πχ, χ(16/κ))`);
* `isGFFWithBoundaryData_cfField`: for a GFF with data `b_C`, the inverted field is a GFF with data
  `counterflowData κ b_C` (the conformal invariance of the zero-boundary GFF under `R`);
* **`isCenteredCounterflowDriver_cfDrv`**: the canonical driver is a centred counterflow driver of `h_C`;
* `ae_trace_of_isCenteredCounterflowDriver`: a centred counterflow with infinite lifetime is almost surely continuous
  from `0` with a complete continuous transient generating trace (Theorem 1.3 at `16/κ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Traverse

open Sec7.StripSysField

/-! ### Conditional kernels -/

/-- `condExpKernel P m` is the conditional kernel given `m ⊓ mΩ` (Mathlib's definition). -/
theorem condExpKernel_eq_inf {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ω₀ : Ω) : condExpKernel P m ω₀ = condExpKernel P (m ⊓ mΩ) ω₀ := by
  have hne : Nonempty Ω := ⟨ω₀⟩
  rw [condExpKernel_apply_eq_condDistrib, condExpKernel_apply_eq_condDistrib]
  have e : m ⊓ mΩ ⊓ mΩ = m ⊓ mΩ := inf_right_idem _ _
  rw [e]

/-- **A `P`-almost sure property holds under almost every conditional law**, for every σ-algebra `m`. -/
theorem ae_ae_condExpKernel {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P m ω₀), p ω := by
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel (𝓔 := m ⊓ mΩ) inf_le_right h] with ω₀ hω₀
  rwa [condExpKernel_eq_inf]

/-! ### The inverted parameter field -/

/-- The infinity-source lift at `R(w) = −1/w`: `ℓ(−1/w) = −2π − ℓ(w)` on `ℍ` (`ℓ = −2 arg`). -/
theorem infinitySourceChart_lift_negInv {w : ℂ} (hw : w ∈ H) :
    infinitySourceChart.2.2 (-w⁻¹) = -(2 * Real.pi) - infinitySourceChart.2.2 w := by
  rw [infinitySourceChart_lift, infinitySourceChart_lift]
  have hw0 : w ≠ 0 := mem_H_ne_zero hw
  have hwim : 0 < w.im := hw
  have him : (w⁻¹).im < 0 := by
    rw [Complex.inv_im]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hwim) (Complex.normSq_pos.2 hw0)
  have hπ : Complex.arg w ≠ Real.pi := (Complex.arg_lt_pi_iff.2 (Or.inr hwim.ne')).ne
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him, Complex.arg_inv]
  simp only [hπ, ↓reduceIte]
  ring

/-- The return chart and the infinity-source chart transport test functions in the same way. -/
theorem pushTest_return_eq_source (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest isConformal_infinityReturnChart φ = Chart.pushTest Chart.isConformal_infinitySourceChart φ := by
  ext z
  rw [Chart.coe_pushTest, Chart.coe_pushTest, coe_dom_infinitySourceChart, coe_dom_infinityReturnChart]
  rfl

/-- The lift term of the infinity-source transport, rewritten in the return-field form. -/
theorem integral_lift_negInv_mul (φ : TestOn upperHalfPlaneOpens) :
    ∫ w, infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ w =
      -(2 * Real.pi) * (∫ w, φ w) - ∫ w, infinitySourceChart.2.2 w * φ w := by
  have hi1 : Integrable (fun z => φ z) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hi2 : Integrable (fun z => infinitySourceChart.2.2 z * φ z) :=
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn continuousOn_infinitySourceChart_lift' φ
      φ.tsupport_subset
  have e : (fun w => infinitySourceChart.2.2 (infinitySourceChart.2.1 w) * φ w) =
      fun w => -(2 * Real.pi) * φ w - infinitySourceChart.2.2 w * φ w := by
    funext w
    by_cases hw : w ∈ H
    · change infinitySourceChart.2.2 (-w⁻¹) * φ w = _
      rw [infinitySourceChart_lift_negInv hw]
      ring
    · have h0 : φ w = 0 := φ.zero_on_compl (show w ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hw)
      rw [h0, mul_zero, mul_zero, mul_zero, sub_zero]
  rw [e, integral_sub (hi1.const_mul _) hi2, integral_const_mul]

/-- **The inverted parameter field** `F_d(f)^R = −f ∘ R + πχ − 2χ arg` of the frozen `IsCenteredCounterflowDriver`
(coefficients `(−1, −πχ, χ(16/κ))` of the infinity-source transport), written as a return field. -/
def cfField (κ : ℝ) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  returnField (cfOffset κ - 2 * Real.pi * cfCoeff κ) (-cfCoeff κ) f

theorem measurable_cfField (κ : ℝ) : Measurable (cfField κ) :=
  measurable_returnField _ _

/-- **`cfField κ f` is the frozen infinity-source transport of `f`.** -/
theorem isChartTransport_cfField (κ : ℝ) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) f
      (cfField κ f) := by
  intro φ φ' hsupp hφ
  rw [Chart.eq_pushTest Chart.isConformal_infinitySourceChart hsupp hφ, cfField, returnField_apply,
    pushTest_return_eq_source, integral_lift_negInv_mul]
  simp only [cfOffset, cfCoeff]
  ring

/-- **The inverted field of a GFF is a GFF with the counterflow data** (`counterflowData κ b`, exceptional set
`{0} ∪ R(jumps)`). -/
theorem isGFFWithBoundaryData_cfField (κ : ℝ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {f : Ω → DistOn upperHalfPlaneOpens} (hf : IsGFFWithBoundaryData Q f b jumps) :
    IsGFFWithBoundaryData Q (fun ω => cfField κ (f ω)) (counterflowData κ b) (counterflowJumps jumps) := by
  have hex : ∃ u, IsBoundedHarmonicExtension b jumps u := by
    obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
    exact ⟨u, hu⟩
  exact isGFFWithBoundaryData_returnField _ _ hex hf

/-! ### The canonical counterflow driver of a field -/

theorem sixteen_div_pos {κ : ℝ} (hκ : 0 < κ) : 0 < 16 / κ := div_pos (by norm_num) hκ

section Canonical

variable (h12p : Exist.Staged.Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (bC : ℝ → ℝ) (jumpsC : Finset ℝ)

/-- The word data of the counterflow word of `bC`: the angle-`0` flow-line word at `16/κ` of `counterflowData κ bC`. -/
def cfWord (κ : ℝ) (bC : ℝ → ℝ) (jumpsC : Finset ℝ) :
    Exist.Staged.WordData (flowLineNL (counterflowData κ bC) (counterflowJumps jumpsC) 0)
      (flowLineNR (counterflowData κ bC) (counterflowJumps jumpsC) 0) :=
  ((flowLineXL (counterflowData κ bC) (counterflowJumps jumpsC) 0,
      flowLineXR (counterflowData κ bC) (counterflowJumps jumpsC) 0),
    (flowLineRhoL (16 / κ) (counterflowData κ bC) (counterflowJumps jumpsC) 0 0,
      flowLineRhoR (16 / κ) (counterflowData κ bC) (counterflowJumps jumpsC) 0 0))

/-- **The canonical centred counterflow of a component field**: the field-determined driver and lifetime of the
counterflow word, read off the flow field of the inverted field. -/
def cfDrv (f : DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  Exist.Staged.drvOf (Exist.Staged.detCode (Exist.Staged.paramΦ h12p (sixteen_div_pos hκ) _ _)
    (cfWord κ bC jumpsC, Exist.flowField 0 (0 * QuantumZipper.chiC (16 / κ)) (cfField κ f)))

theorem measurable_cfDrv : Measurable (cfDrv h12p hκ bC jumpsC) :=
  Exist.Staged.measurable_drvOf.comp ((Exist.Staged.measurable_detCode
    (Exist.Staged.measurable_paramΦ h12p (sixteen_div_pos hκ) _ _)).comp
      (measurable_const.prodMk ((Exist.measurable_flowField 0 _).comp (measurable_cfField κ))))

/-- The canonical driver is continuous before its lifetime and starts at `0`. -/
theorem cfDrv_regular (f : DistOn upperHalfPlaneOpens) :
    ContinuousOn (cfDrv h12p hκ bC jumpsC f).1 {t | (t : ℝ≥0∞) < (cfDrv h12p hκ bC jumpsC f).2} ∧
      (cfDrv h12p hκ bC jumpsC f).1 0 = 0 :=
  ⟨(Exist.Staged.drvOf_regular _).1, (Exist.Staged.drvOf_regular _).2.1⟩

/-- **The canonical driver is a centred counterflow driver** of every GFF `h_C` with piecewise-constant data, under
every probability measure (Theorem 1.2 jointly measurable in the word and Theorem 1.3, through
`Restart.isOptionalHullCoupling_of_detAgree`). -/
theorem isCenteredCounterflowDriver_cfDrv (h13 : Exist.Theorem13Statement.{u})
    (hb : IsPiecewiseConstantBoundaryData bC jumpsC) {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {hC : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData Q hC bC jumpsC) :
    IsCenteredCounterflowDriver κ Q hC (fun t ω => (cfDrv h12p hκ bC jumpsC (hC ω)).1 t)
      (fun ω => (cfDrv h12p hκ bC jumpsC (hC ω)).2) := by
  have hκ' := sixteen_div_pos hκ
  have hb' := isPiecewiseConstant_counterflowData κ hb
  have hh' := isGFFWithBoundaryData_cfField κ hb hh
  have hh₀ := Exist.isGFFWithBoundaryData_flowField hκ' hb' 0 0 hh'
  have hF := Theorem15.isOrderedForceWord_flowLine (counterflowData κ bC) (counterflowJumps jumpsC) 0
  have hD : Measurable fun ω => cfDrv h12p hκ bC jumpsC (hC ω) := (measurable_cfDrv h12p hκ bC jumpsC).comp hh.1
  have hW : ∀ t, Measurable fun ω => (cfDrv h12p hκ bC jumpsC (hC ω)).1 t := fun t =>
    (measurable_pi_apply t).comp (measurable_fst.comp hD)
  have hζ : Measurable fun ω => (cfDrv h12p hκ bC jumpsC (hC ω)).2 := measurable_snd.comp hD
  obtain ⟨𝓕, VL, VR, B, hcoup⟩ := Restart.isOptionalHullCoupling_of_detAgree h12p h13 hκ' hF hh₀ hW hζ
    (Eventually.of_forall fun ω => ⟨rfl, rfl, fun t _ => rfl⟩)
  exact ⟨counterflowData κ bC, counterflowJumps jumpsC, fun ω => cfField κ (hC ω), hb',
    fun ω => isChartTransport_cfField κ (hC ω), _, 𝓕, VL, VR, B,
    fun ω => Exist.isTranslateAddConst_flowField 0 _ _, hcoup⟩

end Canonical

/-! ### Traces of centred counterflows -/

/-- **A centred counterflow with infinite lifetime has a complete continuous transient trace** (Theorem 1.3 at
`16/κ`): almost surely the driver is continuous on `[0, ∞)`, vanishes at `0`, and has a generating trace on `[0, ∞]`
tending to `∞`. -/
theorem ae_trace_of_isCenteredCounterflowDriver (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ Q h W ζ) (hζ : ∀ᵐ ω ∂Q, ζ ω = ⊤) :
    ∀ᵐ ω ∂Q, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ ∃ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧ Tendsto (fun t => ‖γ t‖) atTop atTop := by
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hreg := Supp8.GB6.ae_driver_zero_continuousOn hfl
  obtain ⟨h₀, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have htr := h13 (sixteen_div_pos hκ) (Theorem15.isOrderedForceWord_flowLine b' J' 0) hC.1
  filter_upwards [hreg, htr, hζ] with ω hr ht hζω
  obtain ⟨-, γ, hγ, hγt⟩ := ht
  rw [hζω] at hγ hr
  refine ⟨?_, hr.1, γ, hγ, hγt hζω⟩
  have := hr.2
  simp only [ENNReal.coe_lt_top, ofPred_true] at this
  exact continuousOn_univ.1 this

end GW4Traverse

end Theorem14

end InteractingSLE
