/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513FieldChart
import InteractingSLE.Spec.Sec7.Lemma725RefFullDilField
import InteractingSLE.Spec.Sec7.SideHeightShift
import InteractingSLE.WangWu.ReverseContactLocal
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.Spec.Coupling.Assembly11BProvider
import InteractingSLE.Spec.Supplement.GW2ConeData

/-!
# Local sets of the counterflow's field read back in the strip chart

Packet PROVE-CFRESTART, field side of Lemma 4.7's cross-conditioning (Proposition 3.7 needs both stopped hulls as
local sets of the same field). The counterflow of `IsStripCounterflowDriver` is coupled with its parameter field `h′`
in the chart `M_q` (`Sec4.stripCounterflowChart q`, `M_q(z) = −1 − (1 + q)/z`): `h′` is the chart transport of the
strip field `h` (chart `E`) with sign `−1`, constant `a` and lift coefficient `k`. A local set `K′` of `h′` (the
counterflow hull at a stopping time, by the frozen coupling) is read back in the chart `E` as `M_q⁻¹(K′)`.

* `cfBackTest`: the test-function transport of `M_q⁻¹ = R ∘ (r ·) ∘ (· + 1)` (`r = 1/(1 + q)`) as three landed
  transports (shift, dilation, return chart); **`pushTest_cfBackTest`**: transporting back through `M_q` gives the
  identity; **`integral_mul_cfBackTest`**: the change of variables `∫ u · ψ = ∫ (u ∘ M_q) · φ`;
* **`eq_reflect_of_isChartTransport`**: `h = reflectField (dilField (flowField (−1) 0 h′)) + (a + k · lift)`;
* **`isLocalSet_stripInv_image`**: if `K′` is a local set of `h′`, then `M_q⁻¹(K′)` is a local set of `h` (shift,
  dilation and reflection transports of local sets, PROVE-SEC7-*/WangWu, plus a harmonic shift);
* **`isLocalSet_stripInv_cfHull`**: the counterflow hull of `IsStripCounterflowDriver` at a deterministic time before
  its lifetime, read in the chart `E`, is a local set of the strip field (the strip analogue of
  `GlueCond.isLocalSet_cfHullQ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Sec5.CrossRestart

variable {q : ℝ}

theorem cfr_pos (hq : 0 < q) : 0 < 1 / (1 + q) := by
  have : 0 < 1 + q := by linarith
  positivity

/-- **The test-function transport of `M_q⁻¹`**, as the shift by `1`, the dilation by `1/(1 + q)` and the return chart
`R`: `ψ(z) = |(M_q⁻¹)′(z)|² φ(M_q⁻¹ z)`. -/
def cfBackTest (hq : 0 < q) (φ : TestOn upperHalfPlaneOpens) : TestOn upperHalfPlaneOpens :=
  Chart.pushTest (Exist.isConformal_shiftChart (-1))
    (Chart.pushTest (Chart.isConformal_dilation (cfr_pos hq))
      (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ))

theorem mem_dom_return {w : ℂ} (hw : w ∈ H) :
    w ∈ (Sec7.StripSysField.infinityReturnChart.dom : Set ℂ) := by
  rw [Sec7.StripSysField.isConformal_infinityReturnChart.coe_dom]
  refine ⟨-w⁻¹, WangWu.negInv_mem_H hw, ?_⟩
  show -(-w⁻¹)⁻¹ = w
  rw [inv_neg, inv_inv, neg_neg]

theorem hasDerivAt_stripFwd {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun w : ℂ => -1 - (1 + (q : ℂ)) * w⁻¹) ((1 + (q : ℂ)) * (z ^ 2)⁻¹) z := by
  exact ((hasDerivAt_const z (-1 : ℂ)).sub ((hasDerivAt_inv hz).const_mul (1 + (q : ℂ)))).congr_deriv (by ring)

theorem hasDerivAt_negInv {w : ℂ} (hw : w ≠ 0) : HasDerivAt (fun w : ℂ => -w⁻¹) ((w ^ 2)⁻¹) w := by
  exact (hasDerivAt_inv hw).neg.congr_deriv (by ring)

/-- **Transporting back through `M_q` undoes `cfBackTest`.** -/
theorem pushTest_cfBackTest (hq : 0 < q) (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest (Prop513Field.isConformal hq) (cfBackTest hq φ) = φ := by
  ext z
  rw [Chart.coe_pushTest]
  by_cases hz : z ∈ H
  · have hzd : z ∈ ((Sec4.stripCounterflowChart q).dom : Set ℂ) := by
      rw [Prop513Field.dom_eq hq]; exact hz
    rw [indicator_of_mem hzd]
    have hz0 : z ≠ 0 := WangWu.ne_zero_of_mem_H hz
    have hq1 : (1 + (q : ℂ)) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)
    have hpt : ((1 / (1 + q) : ℝ) : ℂ) * ((Sec4.stripCounterflowChart q).1 z - ((-1 : ℝ) : ℂ)) = -z⁻¹ := by
      rw [Sec4.stripCounterflowChart_fwd]
      push_cast
      field_simp
      ring
    have hRz : -z⁻¹ ∈ H := WangWu.negInv_mem_H hz
    rw [cfBackTest, Exist.pushTest_shiftChart_apply, Sec7.Lemma725RefFull.pushTest_dilation_apply (cfr_pos hq), hpt,
      Chart.coe_pushTest, indicator_of_mem (mem_dom_return hRz)]
    have hRz0 : -z⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hz0)
    change ‖deriv (fun w : ℂ => -1 - (1 + (q : ℂ)) * w⁻¹) z‖ ^ 2 *
      ((1 / (1 + q)) ^ 2 * (‖deriv (fun w : ℂ => -w⁻¹) (-z⁻¹)‖ ^ 2 * φ (-(-z⁻¹)⁻¹))) = φ z
    rw [(hasDerivAt_stripFwd hz0).deriv, (hasDerivAt_negInv hRz0).deriv, inv_neg, inv_inv, neg_neg]
    have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
    have hqn : ‖(1 + (q : ℂ))‖ = 1 + q := by
      rw [← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    simp only [norm_mul, norm_inv, norm_pow, norm_neg, hqn]
    have hq1' : (1 + q) ≠ 0 := by linarith
    field_simp
  · rw [indicator_of_notMem (by rw [Prop513Field.dom_eq hq]; exact hz)]
    exact (φ.zero_on_compl hz).symm

/-- **Change of variables for `cfBackTest`**: `∫ u · ψ = ∫ (u ∘ M_q) · φ`. -/
theorem integral_mul_cfBackTest (hq : 0 < q) (φ : TestOn upperHalfPlaneOpens) (u : ℂ → ℝ) :
    ∫ w, u w * cfBackTest hq φ w = ∫ x, u ((Sec4.stripCounterflowChart q).1 x) * φ x := by
  set χ₁ := Chart.pushTest (Chart.isConformal_dilation (cfr_pos hq))
    (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ) with hχ₁
  have h1 : ∫ w, u w * cfBackTest hq φ w = ∫ y, u (y - 1) * χ₁ y := by
    have e : (fun w => u w * cfBackTest hq φ w) = fun w => (fun y => u (y - 1) * χ₁ y) (w + 1) := by
      funext w
      simp only [cfBackTest, Exist.pushTest_shiftChart_apply, ← hχ₁, add_sub_cancel_right]
      congr 2
      push_cast
      ring
    rw [e, integral_add_right_eq_self (fun y => u (y - 1) * χ₁ y) (1 : ℂ)]
  rw [h1, hχ₁, Sec7.Lemma725RefFull.integral_mul_pushTest_dilation (cfr_pos hq), Chart.integral_mul_pushTest]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show u (-x⁻¹ / ((1 / (1 + q) : ℝ) : ℂ) - 1) * φ x = u ((Sec4.stripCounterflowChart q).1 x) * φ x
  congr 2
  rw [Sec4.stripCounterflowChart_fwd]
  have hq1 : (1 + (q : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)
  push_cast
  field_simp
  ring

/-- The harmonic shift `a + k · lift` of the strip counterflow chart (`lift = Im(−2 log)`). -/
def cfShift (q a k : ℝ) : ℂ → ℝ := fun z => a + k * (Sec4.stripCounterflowChart q).2.2 z

theorem cfShift_eq (q a k : ℝ) : cfShift q a k = fun z => a + k * infinitySourceChart.2.2 z := rfl

theorem continuousOn_cfShift (q a k : ℝ) : ContinuousOn (cfShift q a k) H := by
  rw [cfShift_eq]
  exact continuousOn_const.add (continuousOn_const.mul Sec7.StripSysField.continuousOn_infinitySourceChart_lift')

theorem harmonicOnNhd_cfShift (q a k : ℝ) : InnerProductSpace.HarmonicOnNhd (cfShift q a k) H := by
  rw [cfShift_eq]
  intro z hz
  exact (InnerProductSpace.harmonicAt_const a).add
    (by simpa only [Pi.smul_def, smul_eq_mul] using
      (Sec7.StripSysField.harmonicOnNhd_infinitySourceChart_lift z hz).const_smul (c := k))

/-- **The strip field from the counterflow's parameter field**: if `h′` is the `M_q`-chart transport of `h` with sign
`−1` (`IsChartTransport (stripCounterflowChart q) (−1) a k h h′`), then `h` is the return–dilation–shift transport of
`h′` plus the harmonic shift `a + k · lift`. -/
theorem eq_reflect_of_isChartTransport (hq : 0 < q) {a k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k h h') :
    h = WangWu.reflectField (Sec7.Lemma725RefFull.dilField (cfr_pos hq) (Exist.flowField (-1) 0 h')) +
      smoothDist upperHalfPlaneOpens (cfShift q a k) := by
  ext φ
  have h1 := ht.apply_eq (Prop513Field.isConformal hq) (cfBackTest hq φ)
  rw [pushTest_cfBackTest hq φ] at h1
  have hi1 : ∫ w, cfBackTest hq φ w = ∫ x, φ x := by
    simpa only [one_mul] using integral_mul_cfBackTest hq φ (fun _ => (1 : ℝ))
  have hi2 : ∫ w, (Sec4.stripCounterflowChart q).2.2 ((Sec4.stripCounterflowChart q).2.1 w) * cfBackTest hq φ w =
      ∫ x, (Sec4.stripCounterflowChart q).2.2 x * φ x := by
    rw [integral_mul_cfBackTest]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ H
    · simp only
      rw [Sec4.stripCounterflowChart_inv_fwd hq (WangWu.ne_zero_of_mem_H hx)]
    · simp [φ.zero_on_compl hx]
  have hT : smoothDist upperHalfPlaneOpens (cfShift q a k) φ = a * (∫ x, φ x) +
      k * ∫ x, (Sec4.stripCounterflowChart q).2.2 x * φ x := by
    rw [Coupling.smoothDist_apply_eq (continuousOn_cfShift q a k)]
    have hc0 : Integrable fun w => φ w := by
      simpa only [one_mul] using Coupling.MartMeans2.integrable_mul_test_of_continuousOn (f := fun _ => (1 : ℝ))
        continuousOn_const φ φ.tsupport_subset
    have hc1 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      Sec7.StripSysField.continuousOn_infinitySourceChart_lift' φ φ.tsupport_subset
    simp only [cfShift_eq, add_mul, mul_assoc]
    rw [integral_add (hc0.const_mul a) (hc1.const_mul k), integral_const_mul, integral_const_mul]
    rfl
  show h φ = WangWu.reflectField (Sec7.Lemma725RefFull.dilField (cfr_pos hq) (Exist.flowField (-1) 0 h')) φ +
    smoothDist upperHalfPlaneOpens (cfShift q a k) φ
  rw [WangWu.reflectField_apply, Sec7.Lemma725RefFull.dilField_apply, Exist.flowField_apply, hT]
  have e : Chart.pushTest (Exist.isConformal_shiftChart (-1))
      (Chart.pushTest (Chart.isConformal_dilation (cfr_pos hq))
        (Chart.pushTest Sec7.StripSysField.isConformal_infinityReturnChart φ)) = cfBackTest hq φ := rfl
  rw [e, h1, hi1, hi2]
  ring

/-- `R((z + 1)/(1 + q)) = M_q⁻¹(z)` for every `z` (both are `0` at `z = −1`). -/
theorem negInv_dil_add_one (hq : 0 < q) (z : ℂ) :
    WangWu.negInv (Sec7.Lemma725RefFull.dil (1 / (1 + q)) (z + ((1 : ℝ) : ℂ))) =
      (Sec4.stripCounterflowChart q).2.1 z := by
  have hq1 : (1 + (q : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)
  rw [Sec4.stripCounterflowChart_inv, WangWu.negInv, Sec7.Lemma725RefFull.dil]
  push_cast
  rw [mul_inv, inv_div, div_one]
  ring

/-- **A local set of the counterflow's parameter field, read back in the strip chart, is a local set of the strip
field.** If `h′ ω` is the `M_q`-chart transport of `h ω` with sign `−1` (the field relation of
`Sec4.IsStripCounterflowDriver`) and `A` is a local set of `h′`, then `M_q⁻¹(A)` is a local set of `h`. -/
theorem isLocalSet_stripInv_image (hq : 0 < q) {a k : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} {h h' : Ω → DistOn upperHalfPlaneOpens} (hA : IsLocalSet A h' P)
    (ht : ∀ ω, IsChartTransport (Sec4.stripCounterflowChart q) (-1) a k (h ω) (h' ω)) :
    IsLocalSet (fun ω => (Sec4.stripCounterflowChart q).2.1 '' A ω) h P := by
  have h1 := Sec7.SideHeight.IsLocalSet.translate hA 1
  have h2 := Sec7.Lemma725RefFull.IsLocalSet.dilate (cfr_pos hq) h1
  have h3 := WangWu.IsLocalSet.reflect h2
  have h4 := Coupling.IsLocalSet.add_dist h3
    (WholeField.isHarmonicDistOn_smoothDist (harmonicOnNhd_cfShift q a k))
  have hh : (fun ω => WangWu.reflectField (Sec7.Lemma725RefFull.dilField (cfr_pos hq)
      (Exist.flowField (-(1 : ℝ)) 0 (h' ω))) + smoothDist upperHalfPlaneOpens (cfShift q a k)) = h := by
    funext ω
    rw [show (-(1 : ℝ)) = -1 by norm_num]
    exact (eq_reflect_of_isChartTransport hq (ht ω)).symm
  have hset : (fun ω => WangWu.negInv '' (Sec7.Lemma725RefFull.dil (1 / (1 + q)) ''
      ((fun z : ℂ => z + ((1 : ℝ) : ℂ)) '' A ω))) = fun ω => (Sec4.stripCounterflowChart q).2.1 '' A ω := by
    funext ω
    rw [image_image, image_image]
    exact image_congr fun z _ => negInv_dil_add_one hq z
  rw [hh, hset] at h4
  exact h4

/-- **The strip counterflow hull, read in the chart `E`, is a local set of the strip field** at every deterministic
time `t` before the counterflow's lifetime: `M_q⁻¹(K′_t)` with `K′_t` the hull of the counterflow driver `W` in the
chart `M_q` (frozen local-set clause of the counterflow's coupling, transported by `isLocalSet_stripInv_image`). -/
theorem isLocalSet_stripInv_cfHull (hq : 0 < q) {κ α : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : Sec4.IsStripCounterflowDriver κ α q P h W ζ) (t : ℝ≥0) (ht : ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ζ ω) :
    IsLocalSet (fun ω => (Sec4.stripCounterflowChart q).2.1 ''
      QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) h P := by
  obtain ⟨b', J', h', -, htr, hfl⟩ := hcf
  obtain ⟨h'', 𝓕, VL, VR, B, htac, hC⟩ := hfl
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  obtain ⟨-, -, -, hX, hker⟩ := hC
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := ht
  have hK := (hker (fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ t) hτζ).1
  have hK' : IsLocalSet (fun ω => QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) h'' P := by
    simpa only [WithTop.untopD_coe] using hK
  exact isLocalSet_stripInv_image hq hK' htr

end InteractingSLE.Sec5.CrossRestart
