/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC13Chart
import InteractingSLE.Spec.Sec7.Lemma725RefChartReg

/-!
# Measurability of the original conjugate flow chart

PROVE-SIDE-COLLAR2. Conjugation by the fixed inversion preserves the
measurable domain, forward-map and lift records used by Aux. lemma 119.
All three inherited derivative lifts are retained.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec7.SideC15

open WangWu (negInv)
open SideC12 SideC13

/-- The complete conjugate chart is conformal at every conformal sample. -/
theorem isConformal_conjugate {c : Chart} (hc : c.IsConformal) :
    (conjugateFlowChart c).IsConformal :=
  Chart.isConformal_infinitySourceChart.trans (hc.trans Chart.isConformal_infinitySourceChart)

/-- Conjugation takes exactly the original chart domain to its inversion. -/
theorem dom_conjugate {c : Chart} (hc : c.IsConformal) :
    ((conjugateFlowChart c).dom : Set ℂ) = negInv '' (c.dom : Set ℂ) := by
  rw [(isConformal_conjugate hc).coe_dom, conjugateFlowChart, Chart.trans_image,
    Chart.trans_image, isDomainChart_infinitySourceChart.image_eq, ← hc.coe_dom]
  rfl

/-- A deterministic point belongs to the conjugate domain precisely when
its inversion belongs to the original domain. -/
theorem mem_dom_conjugate_iff {c : Chart} (hc : c.IsConformal) (z : ℂ) :
    z ∈ (conjugateFlowChart c).dom ↔ negInv z ∈ c.dom := by
  rw [← SetLike.mem_coe, dom_conjugate hc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change negInv (negInv y) ∈ (c.dom : Set ℂ)
    rw [WangWu.negInv_negInv]
    exact hy
  · intro h
    exact ⟨negInv z, h, WangWu.negInv_negInv z⟩

variable {Ω : Type*} [MeasurableSpace Ω] {c : Ω → Chart}

/-- Fixed-point domain memberships are measurable in the same record. -/
theorem measurableSet_mem_dom_conjugate (hc : ∀ ω, (c ω).IsConformal)
    (hm : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) (z : ℂ) :
    MeasurableSet {ω | z ∈ (conjugateFlowChart (c ω)).dom} := by
  have he : {ω | z ∈ (conjugateFlowChart (c ω)).dom} = {ω | negInv z ∈ (c ω).dom} :=
    Set.ext fun ω => mem_dom_conjugate_iff (hc ω) z
  rw [he]
  exact hm (negInv z)

/-- Forward values on the conjugate domain are measurable. -/
theorem measurable_fwd_conjugate (hc : ∀ ω, (c ω).IsConformal)
    (hm : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hf : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) (z : ℂ) :
    Measurable ({ω | z ∈ (conjugateFlowChart (c ω)).dom}.indicator
      fun ω => (conjugateFlowChart (c ω)).1 z) := by
  have h := (PocketJordan.measurable_negInv.comp (hf (negInv z))).indicator
    (measurableSet_mem_dom_conjugate hc hm z)
  convert h using 1
  apply indicator_congr
  intro ω hω
  have hdom : ω ∈ {ω | negInv z ∈ (c ω).dom} :=
    (mem_dom_conjugate_iff (hc ω) z).1 hω
  dsimp only [Function.comp_apply]
  rw [conjugateFlowChart_fwd, conjugateFlowMap,
    indicator_of_mem hdom]

/-- The full chain-rule lift is measurable on the conjugate domain. -/
theorem measurable_lift_conjugate (hc : ∀ ω, (c ω).IsConformal)
    (hm : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hf : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hl : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) (z : ℂ) :
    Measurable ({ω | z ∈ (conjugateFlowChart (c ω)).dom}.indicator
      fun ω => (conjugateFlowChart (c ω)).2.2 z) := by
  have hI : Measurable infinitySourceChart.2.2 := by
    have he : infinitySourceChart.2.2 = fun z => -2 * Complex.arg z :=
      funext StripSysField.infinitySourceChart_lift
    rw [he]
    exact measurable_const.mul Complex.measurable_arg
  have h := (((hI.comp (hf (negInv z))).add (hl (negInv z))).add (measurable_const (a := infinitySourceChart.2.2 z))).indicator
    (measurableSet_mem_dom_conjugate hc hm z)
  convert h using 1
  apply indicator_congr
  intro ω hω
  have hdom : ω ∈ {ω | negInv z ∈ (c ω).dom} :=
    (mem_dom_conjugate_iff (hc ω) z).1 hω
  dsimp only [Function.comp_apply, Pi.add_apply]
  rw [conjugateFlowChart_lift, conjugateFlowLift,
    indicator_of_mem hdom,
    indicator_of_mem hdom]

end InteractingSLE.Sec7.SideC15
