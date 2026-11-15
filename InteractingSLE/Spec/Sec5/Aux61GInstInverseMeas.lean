/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstGluedLanding

/-! # Measurability of the selected inverse boundary coordinate -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex MeasureTheory
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData

/-- The inverse at an interior point is the limit of measurable dense-point
selections in the forward chart. No measurability of a chosen inverse is assumed. -/
theorem measurable_chart_inverse {X : Type*} [MeasurableSpace X] {c : X → Chart}
    (hc : ∀ x, (c x).IsConformal) (hm : IsMeasChart c) {w : ℂ} (hw : w ∈ H) :
    Measurable (fun x => (c x).2.1 w) := by
  classical
  let e := TopologicalSpace.denseSeq ℂ
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq ℂ
  have hex : ∀ (n : ℕ) (x : X), ∃ j, e j ∈ (c x).dom ∧
      dist ((c x).1 (e j)) w < 1 / ((n : ℝ) + 1) := by
    intro n x
    have ho : IsOpen (((c x).dom : Set ℂ) ∩ (c x).1 ⁻¹' ball w (1 / ((n : ℝ) + 1))) :=
      (hc x).differentiableOn_fwd.continuousOn.isOpen_inter_preimage (c x).dom.isOpen isOpen_ball
    obtain ⟨j, hj⟩ := he.exists_mem_open ho
      ⟨(c x).2.1 w, (hc x).inv_mem_dom hw, by
        change (c x).1 ((c x).2.1 w) ∈ ball w _
        rw [(hc x).2.2 w hw]
        exact mem_ball_self (by positivity)⟩
    exact ⟨j, hj.1, hj.2⟩
  let N : ℕ → X → ℕ := fun n x => Nat.find (hex n x)
  have hNm : ∀ n, Measurable (N n) := by
    intro n
    apply measurable_find (hex n)
    intro j
    have heq : {x | e j ∈ (c x).dom ∧ dist ((c x).1 (e j)) w < 1 / ((n : ℝ) + 1)} =
        {x | e j ∈ (c x).dom} ∩
          {x | dist (({x | e j ∈ (c x).dom}.indicator fun x => (c x).1 (e j)) x) w <
            1 / ((n : ℝ) + 1)} := by
      ext x
      by_cases hx : e j ∈ (c x).dom <;> simp [hx]
    rw [heq]
    exact (hm.dom _).inter (measurableSet_lt ((hm.fwd _).dist measurable_const) measurable_const)
  refine measurable_of_tendsto_metrizable
    (f := fun n x => e (N n x)) (fun n => (measurable_from_top (f := e)).comp (hNm n)) ?_
  rw [tendsto_pi_nhds]
  intro x
  have hspec : ∀ n, e (N n x) ∈ (c x).dom ∧
      dist ((c x).1 (e (N n x))) w < 1 / ((n : ℝ) + 1) := fun n => Nat.find_spec (hex n x)
  have hg : Tendsto (fun n => (c x).1 (e (N n x))) atTop (𝓝[H] w) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_iff_dist_tendsto_zero.2 ?_,
      Eventually.of_forall fun n => (hc x).fwd_mem (hspec n).1⟩
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hspec n).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hl := ((hc x).1.continuousOn w hw).tendsto.comp hg
  exact hl.congr' (Eventually.of_forall fun n => (hc x).inv_fwd (hspec n).1)

/-- The bounded inverse extension at any real coordinate is measurable on
a measurable event where the extension is continuous. -/
theorem measurable_boundedInverse_real {X : Type*} [MeasurableSpace X]
    {E : Set X} (hE : MeasurableSet E) {c : X → Chart} (hm : IsMeasChart c)
    (hc : ∀ x ∈ E, (c x).IsConformal)
    (hF : ∀ x ∈ E, EqOn (boundedInverse (c x)) (cayley ∘ (c x).2.1) H ∧
      ContinuousOn (boundedInverse (c x)) Hbar) (a : ℝ) :
    Measurable (E.indicator fun x => boundedInverse (c x) (a : ℂ)) := by
  classical
  let w : ℕ → ℂ := fun n => (a : ℂ) + (1 / ((n : ℝ) + 1) : ℝ) * I
  have hw : ∀ n, w n ∈ H := fun n => by
    change 0 < (w n).im
    simp only [w, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
    positivity
  have hwm : ∀ n, Measurable (E.indicator fun x => cayley ((c x).2.1 (w n))) := by
    intro n
    have hi := measurable_chart_inverse (isConformal_chartOf hc) (hm.chartOf hE) (hw n)
    have hcm : Measurable cayley :=
      (measurable_id.sub measurable_const).div (measurable_id.add measurable_const)
    have hci : Measurable (fun x => cayley ((chartOf E c x).2.1 (w n))) :=
      hcm.comp hi
    convert hci.indicator hE using 1
    funext x
    by_cases hx : x ∈ E <;> simp [hx, chartOf_of_mem]
  refine measurable_of_tendsto_metrizable hwm ?_
  rw [tendsto_pi_nhds]
  intro x
  by_cases hx : x ∈ E
  · simp only [indicator_of_mem hx]
    have hl : Tendsto w atTop (𝓝[Hbar] (a : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => QuantumZipper.H_subset_Hbar (hw n)⟩
      simpa only [w, Function.comp_apply, ofReal_zero, zero_mul, add_zero] using
        (tendsto_const_nhds (x := (a : ℂ))).add
          ((Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat |>.mul_const I)
    have hh := ((hF x hx).2 (a : ℂ) (by change 0 ≤ (a : ℂ).im; simp)).tendsto.comp hl
    exact hh.congr' (Eventually.of_forall fun n => (hF x hx).1 (hw n))
  · simp only [indicator_of_notMem hx]
    exact tendsto_const_nhds

end InteractingSLE.Sec5.Aux61GInst
