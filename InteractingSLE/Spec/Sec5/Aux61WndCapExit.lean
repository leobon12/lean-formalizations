/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GCaptureNextExit
import InteractingSLE.Spec.Sec5.Aux61SlitWACRestrict
import InteractingSLE.Spec.Sec5.Aux61SlitWABPieces
import InteractingSLE.Spec.Sec5.Aux61SlitWZRead
import InteractingSLE.Spec.Sec5.Aux61SlitWYTip

/-!
# `PhysicalExit` for the normalized source on finite-buffer record pieces (ruling R102)

Packet PROVE-AUX61-WINDOW. Ruling R102: the fibre cover takes the normalized-capture route
`Aux61Wnd.dyCover_of_normalized_capture`; two of its inputs are `OwnTipForwardLimit` and `PhysicalExit`.

* **`OwnTipForwardLimit`** is already a theorem: `Aux61SlitWY.ownTipForwardLimit S`, from SLITW's
  `SimpleTipForwardLimit` (`Aux61SlitWY.simpleTipForwardLimit`).
* **`PhysicalExit`** (finite contact, or exit from the window before contact, on every restart event) follows from the
  avoidance of the physical-infinity pole on the index's compact buffer by the **normalized** chart at every selected
  record (GLUEINST's `Aux61GCaptureNext.physicalExit_of_finite_buffer`). This is an every-selected-record condition:
  for a
  fixed buffer it fails on records whose chart sends a buffer boundary point to physical infinity (a continuation going
  to infinity inside the window then never exits). It holds on the Borel record piece
  `normFiniteRecords C i B` (certified records whose normalized chart keeps `closure B` off the pole), whose
  measurability is proved here from the normalized chart's continuous inverse extension at every certified record
  (`normalized_record_extension`). Restricting any restart choices to these pieces (`finiteRestrict`, through SLITW's
  `restrictChoices`, which keeps the normalized chart) gives `PhysicalExit` outright (`physicalExit_finiteRestrict`).

Coverage of the window event by the restricted family is part of the existential capture (`hcaptured_cover`, owner
GLUEINST): the capturing candidate must have a pole-free outer buffer, as SLITW's `ae_countable_finite_capture`
provides for the literal chart.

R48: no Theorem 1.2/1.3 input; R77: no post-contact kernel. Nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open QuantumZipper.CA (cayley)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61WndCap

open Aux61SlitW Aux61R1C Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61ULoc LawUnique Aux61SlitWAB
open WangWu (negInv)

universe u

variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- **The normalized chart's two inverse-extension clauses at every certified selected record.** The record's own
regularity and the counterflow trace certificate supply all analytic hypotheses; the domain is the normalized
certificate's retained component. -/
theorem normalized_record_extension (i : C.Idx) {y : SourceRecord S.nL S.nR}
    (hy : y ∈ C.toR1Restart.selected i)
    (hcf : y.1 ∈ counterflowCertified (rationalTime S.s)) :
    EqOn (boundedInverse (Aux61SlitWX.chart C.toR1Restart C.hasChart i y))
        (cayley ∘ (Aux61SlitWX.chart C.toR1Restart C.hasChart i y).2.1) H ∧
      ContinuousOn (boundedInverse (Aux61SlitWX.chart C.toR1Restart C.hasChart i y)) Hbar := by
  have hgood : y ∈ goodSet (rationalTime S.s) (C.q i.1) := hy.2
  obtain ⟨hq, -, -, -, -, hH, hηc, hη0, -⟩ := hgood.1.facts
  have hspec := Aux61SlitWX.chart_spec C.toR1Restart C.hasChart i
  have hdomy := hspec.domain y
  have hb := hspec.base_mem y
  change ((Aux61SlitWX.chart C.toR1Restart C.hasChart i y).dom : Set ℂ) =
    restartComponent (historyHull (rationalTime S.s) (finY (rationalTime S.s) (C.q i.1)) y)
      (finη (rationalTime S.s) (C.q i.1) y) (C.q i.1) (Aux61SlitWX.base C.toR1Restart C.hasChart i y) at hdomy
  change Aux61SlitWX.base C.toR1Restart C.hasChart i y ∈
    retainedDomain (historyHull (rationalTime S.s) (finY (rationalTime S.s) (C.q i.1)) y)
      (finη (rationalTime S.s) (C.q i.1) y) (C.q i.1) at hb
  rw [historyHull, finY_of_mem hgood, finη_of_mem hgood, cfDrv0_eq_frozenDrv hcf.1] at hdomy hb
  have hηH : MapsTo (recη (C.q i.1) y) (Icc 0 (C.q i.1 : ℝ)) Hbar := by
    intro t ht
    rcases ht.1.eq_or_lt with ht0 | ht0
    · rw [← ht0, hη0]
      exact zero_mem_Hbar
    · exact QuantumZipper.H_subset_Hbar (hH ⟨ht0, ht.2⟩)
  have hF := boundedInverse_spec_of_traces
    (hcf.1.isLoewnerTrace_fullTrace hcf.2 (rationalTime_s_pos S))
    (rationalTime S.s).coe_nonneg hηc hηH hb (hspec.conformal y) hdomy
  exact ⟨hF.1, hF.2.1⟩

/-- **The normalized finite-buffer record piece** of an index and a buffer: certified selected records whose
normalized chart keeps the closed buffer off the physical-infinity pole. -/
def normFiniteRecords (i : C.Idx) (B : Set ℂ) : Set (SourceRecord S.nL S.nR) :=
  {y | y ∈ certifiedSelection C i ∧
    ∀ z ∈ closure B ∩ Hbar, boundedInverse (Aux61SlitWX.chart C.toR1Restart C.hasChart i y) z ≠ 1}

/-- The normalized finite-buffer record piece of a compact buffer is Borel. -/
theorem measurableSet_normFiniteRecords (hsel : ∀ i, MeasurableSet (C.selected i)) (i : C.Idx)
    {B : Set ℂ} (hB : IsCompact (closure B)) : MeasurableSet (normFiniteRecords C i B) := by
  have hspec := Aux61SlitWX.chart_spec C.toR1Restart C.hasChart i
  exact Aux61SlitWAA.measurableSet_finite_buffer (measurableSet_certifiedSelection C hsel i)
    hspec.measurable (fun y _ => hspec.conformal y)
    (fun _ hy => normalized_record_extension C i hy.1 hy.2) hB

/-- **`PhysicalExit` of the normalized source** whenever every selected record keeps each index's closed buffer off
the pole under the normalized chart. -/
theorem physicalExit_of_selected_finite (hsel : ∀ i, MeasurableSet (C.selected i))
    (hsub : ∀ i : C.Idx, ∀ y ∈ C.toR1Restart.selected i,
      ∀ z ∈ closure (C.toR1Restart.data i).buffer ∩ Hbar,
        boundedInverse (Aux61SlitWX.chart C.toR1Restart C.hasChart i y) z ≠ 1) :
    Aux61SlitWX.PhysicalExit C.toR1Restart C.hasChart :=
  Aux61GCaptureNext.physicalExit_of_finite_buffer C.toR1Restart C.hasChart (Aux61SlitWZ.readers C hsel)
    fun i => Eventually.of_forall fun _ he z hz => hsub i _ he z hz

open Classical in
/-- **The finite-buffer restriction** of restart choices: at an index with a good record, the normalized
finite-buffer record piece of the index's own buffer. -/
def finiteRestrict : C.ι → Set (SourceRecord S.nL S.nR) := fun i =>
  if hi : (C.good i).Nonempty then normFiniteRecords C ⟨i, hi⟩ (C.data i).buffer else univ

/-- The finite-buffer restriction is Borel. -/
theorem measurableSet_finiteRestrict (hsel : ∀ i, MeasurableSet (C.selected i)) (i : C.ι) :
    MeasurableSet (finiteRestrict C i) := by
  unfold finiteRestrict
  split_ifs with hi
  · exact measurableSet_normFiniteRecords C hsel ⟨i, hi⟩ (C.data i).buffer_compact
  · exact MeasurableSet.univ

/-- The restricted choices keep measurable selection. -/
theorem selected_measurable_finiteRestrict (hsel : ∀ i, MeasurableSet (C.selected i)) :
    ∀ i, MeasurableSet ((Aux61SlitWAC.restrictChoices C (finiteRestrict C)).selected i) :=
  Aux61SlitWAC.selected_measurable_restrict C (finiteRestrict C) hsel (measurableSet_finiteRestrict C hsel)

/-- **`PhysicalExit` for the finite-buffer restriction of any restart choices**, with the normalized chart (unchanged
by the restriction). -/
theorem physicalExit_finiteRestrict (hsel : ∀ i, MeasurableSet (C.selected i)) :
    Aux61SlitWX.PhysicalExit (Aux61SlitWAC.restrictChoices C (finiteRestrict C)).toR1Restart
      (Aux61SlitWAC.restrictChoices C (finiteRestrict C)).hasChart := by
  apply physicalExit_of_selected_finite _ (selected_measurable_finiteRestrict C hsel)
  intro i y hy z hz
  rw [Aux61SlitWAC.normalized_chart_restrict_eq C (finiteRestrict C) i]
  have hA : y ∈ finiteRestrict C i.1 := hy.1.2
  have he : finiteRestrict C i.1 = normFiniteRecords C i (C.data i.1).buffer := by
    unfold finiteRestrict
    exact dite_eq_left i.2
  rw [he] at hA
  exact hA.2 z hz

/-- **The restriction keeps every actual selected record whose normalized chart keeps the index's closed buffer off
the pole** (almost surely; the counterflow certificate holds for every actual record). This is the form in which a
capturing index with a pole-free buffer transports to the restricted family. -/
theorem ae_mem_finiteRestrict (i : C.Idx) : ∀ᵐ p ∂S.μ,
    sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ C.toR1Restart.selected i →
    (∀ z ∈ closure (C.toR1Restart.data i).buffer ∩ Hbar,
      boundedInverse (sourceChart (Aux61SlitWX.source C.toR1Restart C.hasChart) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1) →
    sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      (Aux61SlitWAC.restrictChoices C (finiteRestrict C)).toR1Restart.selected i := by
  filter_upwards [ae_record_mem_certifiedSelection C i] with p hcert hsel hfin
  have he : finiteRestrict C i.1 = normFiniteRecords C i (C.data i.1).buffer := by
    unfold finiteRestrict
    exact dite_eq_left i.2
  refine ⟨⟨hsel.1, ?_⟩, hsel.2⟩
  rw [he]
  exact ⟨hcert hsel, hfin⟩

end InteractingSLE.Sec5.Aux61WndCap
