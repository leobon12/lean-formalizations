/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513BridgeField
import InteractingSLE.Spec.Sec5.CrossRestartKernelLocal

/-!
# A concrete inverse parameter-field frame for Proposition 5.13

The test transport is the landed `CrossRestart.cfBackTest`. Its inverse chart
is the composition of the existing translation, dilation and return charts.
The field constructed here is defined for every distribution, independently of
any field law. Its forward signed transport is exactly the given distribution.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Sec5.Prop513Bridge

open Sec4 CrossRestart Sec7.StripSysField

/-- The inverse of `M_q`, assembled from the landed elementary charts. -/
def backChart (q : ℝ) : Chart :=
  ((Exist.shiftChart (-1)).trans (Chart.dilation (1 / (1 + q)))).trans
    infinityReturnChart

theorem backChart_isConformal {q : ℝ} (hq : 0 < q) : (backChart q).IsConformal :=
  ((Exist.isConformal_shiftChart (-1)).trans
    (Chart.isConformal_dilation (cfr_pos hq))).trans isConformal_infinityReturnChart

theorem pushTest_backChart {q : ℝ} (hq : 0 < q) (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest (backChart_isConformal hq) φ = cfBackTest hq φ := by
  exact (Chart.pushTest_trans
    ((Exist.isConformal_shiftChart (-1)).trans (Chart.isConformal_dilation (cfr_pos hq)))
    isConformal_infinityReturnChart φ).trans
      (Chart.pushTest_trans (Exist.isConformal_shiftChart (-1))
        (Chart.isConformal_dilation (cfr_pos hq)) _)

theorem backChart_inv {q : ℝ} (hq : 0 < q) (z : ℂ) :
    (backChart q).2.1 z = (stripCounterflowChart q).1 z := by
  have hq1 : (1 + (q : ℂ)) ≠ 0 := one_add_ne_zero_of_pos hq
  change -z⁻¹ / ((1 / (1 + q) : ℝ) : ℂ) + (-1 : ℝ) = _
  rw [stripCounterflowChart_fwd]
  push_cast
  field_simp
  ring

theorem backChart_dom {q : ℝ} (hq : 0 < q) :
    (backChart q).dom = upperHalfPlaneOpens := by
  apply SetLike.coe_injective
  rw [(backChart_isConformal hq).coe_dom]
  change (backChart q).2.1 '' H = H
  simp_rw [backChart_inv hq]
  refine Subset.antisymm (image_subset_iff.2 fun z hz =>
    stripCounterflowChart_fwd_mem_H hq hz) ?_
  intro z hz
  refine ⟨(stripCounterflowChart q).2.1 z, stripCounterflowChart_inv_mem_H hq hz, ?_⟩
  exact stripCounterflowChart_fwd_inv hq (fun he => by
    have hi := congrArg Complex.im he
    simp only [Complex.neg_im, Complex.one_im, neg_zero] at hi
    exact (ne_of_gt hz) hi)

/-- A conformal chart's test transport is injective. -/
theorem pushTest_injective {c : Chart} (hc : c.IsConformal) :
    Function.Injective (Chart.pushTest hc) := by
  intro φ ψ he
  ext w
  by_cases hw : w ∈ H
  · have hd := hc.deriv_inv_fwd_mul_deriv_fwd (hc.inv_mem_dom hw)
    have hn : deriv c.1 (c.2.1 w) ≠ 0 := right_ne_zero_of_mul_eq_one hd
    have hev := congrArg (fun f : TestOn upperHalfPlaneOpens => f (c.2.1 w)) he
    rw [Chart.pushTest_apply_of_mem hc φ (hc.inv_mem_dom hw),
      Chart.pushTest_apply_of_mem hc ψ (hc.inv_mem_dom hw), hc.2.2 w hw] at hev
    exact mul_left_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hn)) hev
  · rw [φ.zero_on_compl hw, ψ.zero_on_compl hw]

theorem cfBackTest_pushTest {q : ℝ} (hq : 0 < q) (φ : TestOn upperHalfPlaneOpens) :
    cfBackTest hq (Chart.pushTest (Prop513Field.isConformal hq) φ) = φ := by
  apply pushTest_injective (Prop513Field.isConformal hq)
  exact pushTest_cfBackTest hq _

/-- The source field recovered from its counterflow parameter field:
`-hP ∘ M_q + a + k lift`, with the original deterministic branch. -/
def parameterSource {q : ℝ} (hq : 0 < q) (a k : ℝ)
    (hP : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  -Chart.pullField (backChart_isConformal hq) hP +
    smoothDist upperHalfPlaneOpens (cfShift q a k)

theorem parameterSource_apply {q : ℝ} (hq : 0 < q) (a k : ℝ)
    (hP : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    parameterSource hq a k hP φ = -hP (cfBackTest hq φ) +
      (∫ z, cfShift q a k z * φ z) := by
  rw [parameterSource, add_apply, neg_apply, Chart.pullField_apply,
    pushTest_backChart, Coupling.smoothDist_apply_eq (continuousOn_cfShift q a k)]

theorem measurable_parameterSource {q : ℝ} (hq : 0 < q) (a k : ℝ) :
    Measurable (parameterSource hq a k) :=
  LQGMetric.measurable_distOn_iff.2 fun φ => by
    simp_rw [parameterSource_apply]
    exact (LQGMetric.measurable_distOn_apply (cfBackTest hq φ)).neg.add_const _

/-- The concrete source field has exactly the required forward chart transport. -/
theorem isChartTransport_parameterSource {q : ℝ} (hq : 0 < q) (a k : ℝ)
    (hP : DistOn upperHalfPlaneOpens) :
    IsChartTransport (stripCounterflowChart q) (-1) a k
      (parameterSource hq a k hP) hP := by
  intro φ φ' hsupp hφ
  rw [Chart.eq_pushTest (Prop513Field.isConformal hq) hsupp hφ,
    parameterSource_apply, cfBackTest_pushTest hq]
  have hi := Chart.integral_mul_pushTest (Prop513Field.isConformal hq) φ' (cfShift q a k)
  have hi0 : Integrable (fun z => φ' z) :=
    φ'.continuous.integrable_of_hasCompactSupport φ'.hasCompactSupport
  have hi1 := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
    (Prop513Field.continuousOn_lift_inv hq) φ' φ'.tsupport_subset
  have he : (∫ z, cfShift q a k z * Chart.pushTest (Prop513Field.isConformal hq) φ' z) =
      a * (∫ z, φ' z) +
        k * (∫ z, (stripCounterflowChart q).2.2 ((stripCounterflowChart q).2.1 z) * φ' z) := by
    rw [hi]
    simp only [cfShift, add_mul, mul_assoc]
    rw [integral_add (hi0.const_mul a) (hi1.const_mul k),
      integral_const_mul, integral_const_mul]
  rw [he]
  ring

end InteractingSLE.Sec5.Prop513Bridge
