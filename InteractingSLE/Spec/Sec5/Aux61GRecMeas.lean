/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GVanTransfer
import InteractingSLE.Spec.Sec5.Aux61MarksInit
import Mathlib.MeasureTheory.Measure.Count

/-! # Measurability of the exact universal representative boundary predicate

The existing measurable harmonic correction theorem is applied with counting
measure. Its almost-sure representative identity then holds at every point.
The boundary predicate for all representatives is equivalent to the already
measurable boundary predicate of this one continuous correction.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.Aux61GRec
open Aux61Fib (FibData)

/-- Boundary comparison for every harmonic representative of an everywhere
harmonic measurable distribution family is a measurable event. -/
theorem measurableSet_representative_boundary {α : Type*} [MeasurableSpace α]
    (d : FibData) {T : α → DistOn upperHalfPlaneOpens} (hT : Measurable T)
    (hh : ∀ b, IsHarmonicDistOn (T b) H) :
    MeasurableSet {b | ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (a : ℂ)) (𝓝 0)} := by
  obtain ⟨Q, hQm, hQh, hQr⟩ := Aux61GInst.exists_measurable_initialCorrection
    (μ := Measure.count) d hT (ae_of_all _ hh)
  have hrep := Measure.ae_count_iff.1 hQr
  have hH : H.Nonempty := ⟨Complex.I, by
    simp only [H, mem_ofPred_eq, Complex.I_im, zero_lt_one]⟩
  have hm := Aux61GVan.measurableSet_boundary_zero (F := Q) hH d.O₀_open
    (fun z _ => hQm.comp (measurable_id.prodMk measurable_const))
    (fun b => (hQh b).continuousOn)
  convert hm using 1
  ext b
  constructor
  · intro hb
    obtain ⟨v, hv, hp⟩ := hh b
    have hp' : ∀ ψ : TestOn upperHalfPlaneOpens, T b ψ = ∫ z, v z * ψ z :=
      fun ψ => hp ψ ψ.tsupport_subset
    intro a ha
    refine (hb v hv hp' a ha).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have he := hrep b v hv hp' hz
    dsimp only at he ⊢
    linarith only [he]
  · intro hb v hv hp a ha
    refine (hb a ha).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have he := hrep b v hv hp hz
    dsimp only at he ⊢
    linarith only [he]

/-- The precise good-record boundary predicate used by MARKS is measurable,
including its harmonicity premise. No law on records is needed. -/
theorem measurableSet_record_boundary {β : Type*} [MeasurableSpace β]
    (d : FibData) {B : Set β} (hB : MeasurableSet B) :
    MeasurableSet {b : β × DistOn upperHalfPlaneOpens |
      b.1 ∈ B → IsHarmonicDistOn b.2 H → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v H →
      (∀ ψ : TestOn upperHalfPlaneOpens, b.2 ψ = ∫ z, v z * ψ z) →
      ∀ a ∈ d.O₀, Tendsto (fun z => v z - Aux61GlueK.refMean0 d z)
        (𝓝[H] (a : ℂ)) (𝓝 0)} := by
  have hm := measurableSet_representative_boundary d
    (Aux61Marks.measurable_initialDist d hB) (Aux61Marks.initialDist_harmonic d B)
  have hG := Aux61Marks.measurableSet_initialGood hB
  convert hG.compl.union hm using 1
  ext b
  by_cases hb : b ∈ Aux61Marks.initialGood B
  · simp only [mem_ofPred_eq, mem_union, mem_compl_iff, hb, not_true_eq_false,
      false_or, Aux61Marks.initialDist_of_mem hb]
    exact ⟨fun h => h hb.1 hb.2, fun h _ _ => h⟩
  · have hnot : ¬ (b.1 ∈ B ∧ IsHarmonicDistOn b.2 H) := hb
    simp only [mem_union, mem_compl_iff, hb, not_false_eq_true, true_or, iff_true,
      mem_ofPred_eq]
    exact fun h₁ h₂ => (hnot ⟨h₁, h₂⟩).elim

end InteractingSLE.Sec5.Aux61GRec
