/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleTarget

/-! # The E-to-Q chart and its inherited argument -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Target

open QuantumZipper Sec4 Sec7.StripSysField Prop513Schedule

/-- The intermediate inverse coordinate, before the initial translation. -/
def middle (q : ℝ) (z : ℂ) : ℂ := (stripCounterflowChart q).2.1 (z - 2)

/-- The real inverse boundary coordinate of the E-to-Q chart. -/
def realInv (q x : ℝ) : ℝ := -(1 + q) / (x - 1) - (1 + q)

/-- The real intermediate boundary coordinate. -/
def realMiddle (q x : ℝ) : ℝ := -(1 + q) / (x - 1)

theorem inv_eq (q : ℝ) (z : ℂ) :
    (targetChart q).2.1 z = middle q z - (1 + q) := by
  simp only [targetChart, Chart.trans, Chart.recenter, Chart.id, middle,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one]
  congr 1

theorem lift_inv_eq (q : ℝ) (z : ℂ) :
    (targetChart q).2.2 ((targetChart q).2.1 z) = infinitySourceChart.2.2 (middle q z) := by
  simp only [targetChart, Chart.trans, Chart.recenter, Chart.id,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one, middle, zero_add, add_zero,
    ← sub_eq_add_neg, sub_neg_eq_add, sub_add_cancel]
  rfl

theorem middle_mem_H {q : ℝ} (hq : 0 < q) {z : ℂ} (hz : z ∈ H) : middle q z ∈ H :=
  stripCounterflowChart_inv_mem_H hq (by simpa [H] using hz)

theorem dom_eq {q : ℝ} (hq : 0 < q) : (targetChart q).dom = upperHalfPlaneOpens := by
  apply SetLike.coe_injective
  rw [(targetChart_isConformal hq).coe_dom]
  change (targetChart q).2.1 '' H = H
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨w, hw, rfl⟩
    exact (targetChart_isConformal hq).2.1 hw
  intro z hz
  have hv : z + (1 + (q : ℂ)) ∈ H := by
    simpa [H] using hz
  obtain ⟨w, hw, he⟩ := (image_stripCounterflowChart_inv hq).superset hv
  refine ⟨w + 2, ?_, ?_⟩
  · simpa [H] using hw
  · rw [inv_eq, middle, add_sub_cancel_right, he, add_sub_cancel_right]

theorem middle_ofReal (q x : ℝ) : middle q (x : ℂ) = (realMiddle q x : ℝ) := by
  simp only [middle, stripCounterflowChart, realMiddle, div_eq_mul_inv,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_sub, Complex.ofReal_inv]
  congr 2
  ring

theorem inv_ofReal (q x : ℝ) : (targetChart q).2.1 (x : ℂ) = (realInv q x : ℝ) := by
  rw [inv_eq, middle_ofReal]
  simp only [realInv, realMiddle, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one]

theorem realMiddle_ne_zero {q x : ℝ} (hq : 0 < q) (hx : x ≠ 1) :
    realMiddle q x ≠ 0 := div_ne_zero (neg_ne_zero.2 (by linarith)) (sub_ne_zero.2 hx)

theorem tendsto_middle_H {q x : ℝ} (hq : 0 < q) (hx : x ≠ 1) :
    Tendsto (middle q) (𝓝[H] (x : ℂ)) (𝓝[H] (realMiddle q x : ℂ)) := by
  have hshift : Tendsto (fun z : ℂ => z - 2) (𝓝[H] (x : ℂ)) (𝓝[H] ((x - 2 : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · convert
        (((continuous_id.sub continuous_const : Continuous (fun z : ℂ => z - 2)).tendsto
          (x : ℂ)).mono_left nhdsWithin_le_nhds) using 1 <;> norm_num
      rfl
    · simpa [H] using hz
  convert (Prop513Field.tendsto_inv_H hq (x := x - 2) (fun he => hx (by linarith))).comp hshift using 1
  congr 2
  dsimp only [Prop513Field.realInv, realMiddle]
  congr 1
  ring_nf

theorem tendsto_inv_H {q x : ℝ} (hq : 0 < q) (hx : x ≠ 1) :
    Tendsto (targetChart q).2.1 (𝓝[H] (x : ℂ)) (𝓝[H] (realInv q x : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_,
    eventually_nhdsWithin_of_forall fun z hz => (targetChart_isConformal hq).2.1 hz⟩
  have hm := (tendsto_middle_H hq hx).mono_right nhdsWithin_le_nhds
  convert hm.sub_const (1 + (q : ℂ)) using 1
  · exact funext (inv_eq q)
  · simp only [realInv, realMiddle, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one]

/-- The chart lift is the logarithmic inversion lift in the middle coordinate. -/
theorem continuousOn_lift_inv {q : ℝ} (hq : 0 < q) :
    ContinuousOn (fun z => (targetChart q).2.2 ((targetChart q).2.1 z)) H := by
  simp_rw [lift_inv_eq]
  exact continuousOn_infinitySourceChart_lift'.comp
    ((Prop513Field.isConformal hq).1.continuousOn.comp
      (continuousOn_id.sub continuousOn_const) (fun z hz => by
        simpa [H] using hz))
    (fun z hz => middle_mem_H hq hz)

end InteractingSLE.Sec5.Prop513Target
