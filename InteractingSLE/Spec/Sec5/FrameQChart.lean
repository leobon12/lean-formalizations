/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetGeometry
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Sec5.CrossCondStagedMean

/-!
# The Figure 5.1 E-to-Q change of frame

The canonical field law is already `Prop513Target.gff`. Here the inherited
lift of `R ∘ T_q` is identified with that of `M_q`, including its integer
argument. This gives the counterflow-driver identity without a time change.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.FrameQ

open QuantumZipper Sec4 Prop513Schedule Prop513Target
open LQGMetric (DistOn)

/-- The concrete E-to-Q forward map on its nonsingular domain. -/
theorem targetChart_fwd {q : ℝ} {z : ℂ} (hz : z + (1 + (q : ℂ)) ≠ 0) :
    (targetChart q).1 z = z / (z + (1 + q)) := by
  simp only [targetChart, Chart.trans, Chart.recenter, Chart.id, stripCounterflowChart,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one, sub_neg_eq_add]
  norm_num only [Complex.ofReal_ofNat]
  field_simp
  ring

/-- The inherited target-chart lift is the inversion lift after translation. -/
theorem targetChart_lift (q : ℝ) (z : ℂ) :
    (targetChart q).2.2 z = -2 * Complex.arg (z + (1 + q)) := by
  simp only [targetChart, Chart.trans, Chart.recenter, Chart.id, stripCounterflowChart,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one, zero_add, add_zero,
    sub_neg_eq_add]
  norm_num [Complex.mul_im, Complex.log_im]

/-- The two upper-half-plane arguments have a difference in the principal range. -/
theorem arg_div_of_mem_H {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H) :
    Complex.arg (z / w) = Complex.arg z - Complex.arg w := by
  have hz0 := DerivLog.ne_zero_of_mem_H hz
  have hw0 := DerivLog.ne_zero_of_mem_H hw
  have hzarg := Complex.arg_nonneg_iff.2 hz.le
  have hwarg := Complex.arg_nonneg_iff.2 hw.le
  have hzpi := Complex.arg_lt_pi_iff.2 (Or.inr (ne_of_gt hz))
  have hwpi := Complex.arg_lt_pi_iff.2 (Or.inr (ne_of_gt hw))
  have he := Complex.arg_div_coe_angle hz0 hw0
  have hr : Complex.arg z - Complex.arg w ∈ Ioc (-π) π :=
    ⟨by linarith only [hzarg, hwpi], by linarith only [hwarg, hzpi]⟩
  have hreal := congrArg Real.Angle.toReal he
  rw [Complex.arg_coe_angle_toReal_eq_arg, ← Real.Angle.coe_sub,
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.2 hr] at hreal
  exact hreal

/-- `R ∘ T_q = M_q` on the half-plane, including the inherited lift. -/
theorem target_infinity_fwd_lift {q : ℝ} {z : ℂ} (hz : z ∈ H) :
    (targetChart q |>.trans infinitySourceChart).1 z = (stripCounterflowChart q).1 z ∧
      (targetChart q |>.trans infinitySourceChart).2.2 z = (stripCounterflowChart q).2.2 z := by
  have hzc : z + (1 + (q : ℂ)) ∈ H := by simpa [H] using hz
  have hz0 := DerivLog.ne_zero_of_mem_H hz
  have hzc0 := DerivLog.ne_zero_of_mem_H hzc
  constructor
  · rw [Chart.trans_fst, targetChart_fwd hzc0, stripCounterflowChart_fwd]
    change -(z / (z + (1 + (q : ℂ))))⁻¹ = -1 - (1 + q) * z⁻¹
    field_simp
    ring
  · rw [Chart.trans_lift, targetChart_fwd hzc0, targetChart_lift,
      stripCounterflowChart_lift]
    change (-2 * Complex.log (z / (z + (1 + (q : ℂ))))).im +
      -2 * Complex.arg (z + (1 + q)) = -2 * Complex.arg z
    rw [Complex.mul_im, Complex.log_im, arg_div_of_mem_H hz hzc]
    norm_num
    ring

/-- The inverse coordinate of `R ∘ T_q` is exactly the strip inverse on `ℍ`. -/
theorem target_infinity_inv {q : ℝ} (hq : 0 < q) {w : ℂ} (hw : w ∈ H) :
    (targetChart q |>.trans infinitySourceChart).2.1 w = (stripCounterflowChart q).2.1 w := by
  have hC := (targetChart_isConformal hq).trans Chart.isConformal_infinitySourceChart
  have hz := hC.2.1 hw
  have hf := (target_infinity_fwd_lift (q := q) hz).1
  rw [hC.2.2 w hw] at hf
  exact (stripCounterflowChart_inv_fwd hq (DerivLog.ne_zero_of_mem_H hz)).symm.trans
    (congrArg (stripCounterflowChart q).2.1 hf.symm)

/-- A centered parameter-field transport in Q is the original strip transport. -/
theorem isChartTransport_strip_of_centered {κ q : ℝ} (hκ : 0 < κ) (hq : 0 < q)
    {f f' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport infinitySourceChart (-1) (-(π * chiC κ))
      (chiC (16 / κ)) (targetField κ q hq f) f') :
    IsChartTransport (stripCounterflowChart q) (-1) (-(π * chiC κ))
      (chiC (16 / κ)) f f' := by
  have hQ := targetChart_isConformal hq
  have hR := Chart.isConformal_infinitySourceChart
  have hℓQ := continuousOn_lift_inv hq
  have hℓR := Chart.continuousOn_infinitySourceChart_lift
  have htQ := Chart.isChartTransport_chartTransport hQ
    (Chart.locallyIntegrableOn_of_continuousOn hℓQ) 1 0 (chiC κ) f
  have htR : IsChartTransport infinitySourceChart (-1) (-(π * chiC κ))
      ((-1) * chiC κ) (targetField κ q hq f) f' := by
    simpa only [chiC_sixteen_div hκ, neg_one_mul] using ht
  have htC := Theorem14.GW2JointKernel.isChartTransport_trans_sign hQ hR hℓQ hℓR htQ htR
  have hcC := hQ.trans hR
  have he := CrossCond.Staged.isChartTransport_congr_dom hcC.isOpen_image
    (fun w hw => target_infinity_inv hq hw)
    (fun z hz => (target_infinity_fwd_lift (q := q) (by
      obtain ⟨w, hw, rfl⟩ := hz
      exact hcC.2.1 hw)).1)
    (fun z hz => (target_infinity_fwd_lift (q := q) (by
      obtain ⟨w, hw, rfl⟩ := hz
      exact hcC.2.1 hw)).2) htC
  simpa only [mul_one, mul_zero, zero_add, neg_one_mul, chiC_sixteen_div hκ] using he

/-- Exact equivalence of the two parameter-field descriptions, with the same field version. -/
theorem isChartTransport_strip_iff_centered {κ q : ℝ} (hκ : 0 < κ) (hq : 0 < q)
    {f f' : DistOn upperHalfPlaneOpens} :
    IsChartTransport (stripCounterflowChart q) (-1) (-(π * chiC κ))
        (chiC (16 / κ)) f f' ↔
      IsChartTransport infinitySourceChart (-1) (-(π * chiC κ))
        (chiC (16 / κ)) (targetField κ q hq f) f' := by
  refine ⟨fun ht => ?_, isChartTransport_strip_of_centered hκ hq⟩
  have hR := Chart.isConformal_infinitySourceChart
  have hY := Chart.isChartTransport_chartTransport hR
    (Chart.locallyIntegrableOn_of_continuousOn Chart.continuousOn_infinitySourceChart_lift)
    (-1) (-(π * chiC κ)) (chiC (16 / κ)) (targetField κ q hq f)
  have he := ht.unique (Prop513Field.isConformal hq)
    (isChartTransport_strip_of_centered hκ hq hY)
  rw [he]
  exact hY

/-- The Figure 5.1 driver is the centered counterflow of the actual Q field.
The driver and its lifetime are identical, so capacity time is preserved. -/
theorem isStripCounterflowDriver_iff_centered {κ q : ℝ} (hκ : 0 < κ) (hq : 0 < q)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    IsStripCounterflowDriver κ 0 q P h W ζ ↔
      IsCenteredCounterflowDriver κ P (fun ω => targetField κ q hq (h ω)) W ζ := by
  constructor
  · rintro ⟨b, J, f, hb, ht, hf⟩
    refine ⟨b, J, f, hb, fun ω => ?_, hf⟩
    apply (isChartTransport_strip_iff_centered hκ hq).1
    simpa only [zero_add] using ht ω
  · rintro ⟨b, J, f, hb, ht, hf⟩
    refine ⟨b, J, f, hb, fun ω => ?_, hf⟩
    simpa only [zero_add] using (isChartTransport_strip_iff_centered hκ hq).2 (ht ω)

end InteractingSLE.Sec5.FrameQ
