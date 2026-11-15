/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWABExtension
import InteractingSLE.Spec.Sec5.Aux61SlitWAABufferMeas

/-! # Concrete initial-record pieces with finite physical buffers

The extension and measurability hypotheses of the generic finite-buffer
test are discharged for the literal selected chart. Certification loses
no selected physical sample almost surely.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAB
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61ULoc LawUnique
open Aux61GWord
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- Selected initial records with the finite counterflow trace certificate. -/
def certifiedSelection (i : C.Idx) : Set (SourceRecord S.nL S.nR) :=
  C.toR1Restart.selected i ∩ Prod.fst ⁻¹' counterflowCertified (rationalTime S.s)

theorem measurableSet_certifiedSelection (hsel : ∀ i, MeasurableSet (C.selected i)) (i : C.Idx) :
    MeasurableSet (certifiedSelection C i) :=
  (C.selected_measurable hsel i).inter ((measurableSet_counterflowCertified _).preimage measurable_fst)

/-- The extra trace certification holds on every actual selected record
almost surely, independently of chart normalization. -/
theorem ae_record_mem_certifiedSelection : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      C.toR1Restart.selected i →
    sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      certifiedSelection C i := by
  intro i
  filter_upwards [S.counterflow_good] with p hp he
  exact ⟨he, stopRec_mem_counterflowCertified hp.1 (rationalTime S.s)⟩

/-- The initial records for which a fixed countable candidate has a
compact outer buffer avoiding physical infinity. -/
def finiteBufferRecords (i : C.Idx) (j : SeedWindowIndex) : Set (SourceRecord S.nL S.nR) :=
  {y | y ∈ certifiedSelection C i ∧ ∀ z ∈ closure (outerBuffer j) ∩ Hbar,
    boundedInverse (C.toR1Restart.chart C.hasChart i y) z ≠ 1}

/-- Measurability of the actual chosen chart's finite-buffer record
pieces. No inverse-extension hypothesis is supplied by the caller. -/
theorem measurableSet_finiteBufferRecords (hsel : ∀ i, MeasurableSet (C.selected i))
    (i : C.Idx) (j : SeedWindowIndex) : MeasurableSet (finiteBufferRecords C i j) :=
  Aux61SlitWAA.measurableSet_finite_buffer (measurableSet_certifiedSelection C hsel i)
    (C.toR1Restart.chart_spec C.hasChart i).1
    (fun y _ => (C.toR1Restart.chart_spec C.hasChart i).2.1 y)
    (fun _ hy => record_extension C i hy.1 hy.2) j.property.2.2.2

/-- The criterion is measurable in exactly the sigma algebra generated
by the initial retained record, with no future path coordinate. -/
theorem measurableSet_finiteBuffer_event (hsel : ∀ i, MeasurableSet (C.selected i))
    (i : C.Idx) (j : SeedWindowIndex) :
    MeasurableSet[(inferInstance : MeasurableSpace (SourceRecord S.nL S.nR)).comap
      (sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)]
      ((sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i) ⁻¹'
        finiteBufferRecords C i j) :=
  MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_finiteBufferRecords C hsel i j, rfl⟩

/-- Every record in the piece has a bounded physical inverse-window
image. This is the geometric bound used in the physical-stop field. -/
theorem isBounded_inverse_on_finiteBufferRecords (i : C.Idx) (j : SeedWindowIndex)
    {y : SourceRecord S.nL S.nR} (hy : y ∈ finiteBufferRecords C i j) :
    Bornology.IsBounded ((C.toR1Restart.chart C.hasChart i y).2.1 '' (bufferedWindow j ∩ H)) :=
  Aux61GR1F.isBounded_inverse_window ((C.toR1Restart.chart_spec C.hasChart i).2.1 y)
    (fun _ hz => j.property.2.2.1 (subset_closure hz.1)) j.property.2.2.2
    (record_extension C i hy.1.1 hy.1.2).2 hy.2

end InteractingSLE.Sec5.Aux61SlitWAB
