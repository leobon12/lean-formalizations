/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZFields

/-! # Physical exit from a finite buffer for the exact choice family

The chosen chart's bounded inverse is continuous on the closed half-plane
from its physical retained component, independently of chart normalization.
Avoiding its pole on the existing compact fibre buffer then gives the exact
physical-stop field from the previous module.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 Aux61FibData Aux61GInst Aux61ULoc LawUnique
open WangWu (negInv)
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The literal `ChoiceInputs` chart has the continuous bounded inverse
extension. No selected-set measurability or chart-normalization input is needed. -/
theorem ae_boundedInverse_continuous : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
    ContinuousOn (boundedInverse
      (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) Hbar := by
  have hrd := Aux61GR1F.recordDomainComponent_of_prefix_readers C.toR1Restart C.hasChart
    C.record_Y C.record_η C.q_nonneg
  have hdomain := dom_component_of_record S C.fam hrd (fun _ => Eventually.of_forall fun _ => rfl)
  intro i
  filter_upwards [hdomain i, S.physical_path, S.counterflow_good] with p hd hp hcf he
  obtain ⟨b, hbdom⟩ := hd he
  have hK := GlueCond.cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  change ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
    restartComponent (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) b at hbdom
  have hc := (C.toR1Restart.chart_spec C.hasChart i).2.1
    (sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  have hb : b ∈ retainedDomain (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, hc.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hηH : MapsTo (fun t : ℝ => S.path p.1 t.toNNReal)
      (Icc 0 (rationalTime (C.toR1Restart.q i) : ℝ)) Hbar := by
    intro t ht
    rcases ht.1.eq_or_lt with ht0 | ht0
    · rw [← ht0]
      change S.path p.1 (0 : ℝ).toNNReal ∈ Hbar
      rw [hp.2.2.zero]
      exact zero_mem_Hbar
    · exact QuantumZipper.H_subset_Hbar (hp.2.2.mem_H t ht0)
  exact (boundedInverse_spec_of_traces (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2
    (rationalTime S.s).coe_nonneg (hp.2.2.cont.mono Icc_subset_Ici_self) hηH hb hc hbdom).2.1

/-- The exact physical-stop field using the existing fibre buffer.
Its finite-image condition is the remaining physical window input. -/
theorem physical_stop_of_finite_buffer (hsel : ∀ i, MeasurableSet (C.selected i))
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (GlueCond.cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (hfinite : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → ∀ z ∈ closure (C.toR1Restart.data i).buffer ∩ Hbar,
      boundedInverse (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1) :
    ∀ i, ∀ᵐ p ∂S.μ, sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      C.toR1Restart.selected i → p ∈ C.fam.event i ∧ 0 < C.fam.contact i p ∧
      (C.fam.contact i p < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < C.fam.contact i p ∧
        inPath (C.fam.event i)
          (sourceChart (withRecordPath S C.fam) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          ((withRecordPath S C.fam).path i) (C.fam.contact i) p v ∉ (C.toR1Restart.data i).V) := by
  apply physical_stop_of_chart_geometry C hsel hg
  intro i
  filter_upwards [ae_boundedInverse_continuous C i, hfinite i] with p hc hf he
  exact Aux61GR1F.isBounded_inverse_window ((C.toR1Restart.chart_spec C.hasChart i).2.1 _)
    (C.toR1Restart.data i).V_sub (C.toR1Restart.data i).buffer_compact (hc he) (hf he)

end InteractingSLE.Sec5.Aux61SlitWZ
