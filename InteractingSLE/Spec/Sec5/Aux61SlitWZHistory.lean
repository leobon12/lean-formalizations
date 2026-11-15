/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CActual
import InteractingSLE.Spec.Sec5.Aux61GR1FHistory

/-! # The good-record part of the exact `ChoiceInputs.history_cover`

The source window event makes its actual retained record at the original
restart time good. Thus a cover by selected records at that same rational
time already has the good-record certificate required by `ChoiceInputs`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61R1C Aux61Restart Aux61Asm2 Aux61ULoc LawUnique GlueCond
universe u

/-- The actual source window supplies the good-record certificate at its
original rational own time; no additional record-regularity input remains. -/
theorem ae_window_good_record (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → actRec S S.t p ∈ goodSet (rationalTime S.s) S.t := by
  filter_upwards [Aux61GR1F.ae_source_window_configuration S, ae_mem_goodSet_of_frequent S,
    ae_mem_goodCfSet S] with p hconfig hgood hcf hwin
  have hK : historyHull (rationalTime S.s) (fun p : S.Ω × HistorySpace 0 0 => p.2) p =
      cfHullQ (rationalTime S.s) p.2 := by
    change WangWu.negInv '' QuantumZipper.fwdHull (CrossCond.Word49.cfDrv0 _ p.2) _ = _
    rw [CrossCond.Word49.fwdHull_cfDrv0 hcf,
      ← cfHullQ_eq_of_mem_goodCfSet hcf (rationalTime S.s)]
  have hc := hconfig hwin
  have hclear := hc.1.2.2
  obtain ⟨b, hb, hf⟩ := hc.2.2
  rw [hK] at hclear hb hf
  refine hgood S.t S.t_pos hclear b hb ?_
  change ∃ᶠ w in 𝓝[H] 0, fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1)
    (rationalTime S.t) w ∈ _ at hf
  rwa [coe_rationalTime S.t_pos.le] at hf

variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The exact history-cover field, reduced to covering by selected records
at the original time. The required good-record conjunct is proved. -/
theorem history_cover_of_same_time_selection
    (hcover : ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, C.q i = S.t ∧ C.record i p ∈ C.selected i) :
    ∀ᵐ p ∂S.μ, S.windowEvent p →
      ∃ i, C.record i p ∈ C.selected i ∧ C.record i p ∈ C.good i := by
  filter_upwards [ae_window_good_record S, hcover] with p hgood hsel hwin
  obtain ⟨i, hi, hs⟩ := hsel hwin
  refine ⟨i, hs, ?_⟩
  change actRec S (C.q i) p ∈ goodSet (rationalTime S.s) (C.q i)
  rw [hi]
  exact hgood hwin

end InteractingSLE.Sec5.Aux61SlitWZ
