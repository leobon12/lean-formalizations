/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZPoint

/-! # The topology fields of chart geometry for the literal choice family

The retained-component identity, positive restart time, retained-domain
containment and simple connectedness hold independently of normalization
of the chosen chart. The remaining normalization fields are not inferred.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 Aux61ULoc LawUnique
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The exact record-domain component for the chart used by `ChoiceInputs`. -/
theorem record_domain : RecordDomainComponent S C.fam :=
  Aux61GR1F.recordDomainComponent_of_prefix_readers C.toR1Restart C.hasChart
    C.record_Y C.record_η C.q_nonneg

/-- Its physical component identity holds on the selected event almost surely. -/
theorem ae_domain : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → ∃ b : ℂ,
    ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
      restartComponent (GlueCond.cfHullQ (rationalTime S.s) p.2)
        (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) b :=
  dom_component_of_record S C.fam (record_domain C) (fun _ => Eventually.of_forall fun _ => rfl)

/-- Three fields of `SourceChartGeometry` for the actual chosen chart:
positive time, physical retained containment and simple connectedness. -/
theorem ae_chart_topology : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
    0 < rationalTime (C.toR1Restart.q i) ∧
      ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) ⊆
        H \ (GlueCond.cfHullQ (rationalTime S.s) p.2 ∪
          (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (rationalTime (C.toR1Restart.q i) : ℝ)) ∧
      IsSimplyConnected
        ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) := by
  intro i
  filter_upwards [ae_domain C i, S.physical_path, S.counterflow_retained_geometry] with p hd hp hcf he
  obtain ⟨b, hbdom⟩ := hd he
  have hc := (C.toR1Restart.chart_spec C.hasChart i).2.1
    (sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  have hb : b ∈ retainedDomain (GlueCond.cfHullQ (rationalTime S.s) p.2)
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, hc.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  obtain ⟨y, hy⟩ := i.2
  have hpos : 0 < rationalTime (C.toR1Restart.q i) := Real.toNNReal_pos.2 hy.1.facts.1
  refine ⟨hpos, ?_, ?_⟩
  · rw [hbdom]
    exact connectedComponentIn_subset _ _
  · rw [hbdom]
    exact (restartComponent_properties (rationalTime (C.toR1Restart.q i)).coe_nonneg
      (hcf (rationalTime S.s)).2.1 (hcf (rationalTime S.s)).2.2.1
      (hp.2.2.cont.mono Icc_subset_Ici_self) hp.2.2.zero hb).2.2.1

end InteractingSLE.Sec5.Aux61SlitWZ
