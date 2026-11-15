/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow18Windows

/-! # The capturing index survives the normalized finite restriction

The landed existential capture uses the same retained time chart, record
pieces, contact, continuation window and landing interval. Only O₀ has
changed, so the actual capturing index is retained without another choice.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow18
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData LawUnique
universe u

/-- Every actual record selected by the landed capturing family survives
the exact finite restriction in the current route. -/
theorem capturing_record_survives (S : SourceSetting.{u}) (i : (choices S).Idx)
    (p : S.Ω × HistorySpace 0 0)
    (hp : p ∈ (Aux61GWindow17.refinedFamily S).event i) :
    sourceRecord (family S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      (finiteChoices S).toR1Restart.selected i :=
  selected_survives_finite S i hp

/-- The same index captures the actual continuation after restricting
both the seed collar and the finite buffer at the initial record. -/
theorem family_completed_cover (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → ∃ i, Aux61GRec.completedCapture (S.marksData (family S)) i p := by
  filter_upwards [Aux61GWindow17.refinedFamily_completed_cover S] with p hc hw
  obtain ⟨i, hi, hf, hs, y, hy, hl⟩ := hc hw
  refine ⟨i, capturing_record_survives S i p hi, hf, ?_, y, hy, ?_⟩
  · intro v hv
    change inPath ((family S).event i)
      (sourceChart (family S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family S).path i) ((family S).contact i) p v ∈ ((family S).data i).V
    rw [family_inPath_eq S i p]
    exact hs v hv
  · change Tendsto (inPath ((family S).event i)
      (sourceChart (family S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family S).path i) ((family S).contact i) p)
      (𝓝[<] ((family S).contact i p).toNNReal) (𝓝 (y : ℂ))
    rw [family_inPath_eq S i p]
    exact hl

/-- The exact existential capture input of
`Aux61WndCap.dyCover_of_finiteRestrict_capture`. The regularity cut is
conull, and the capturing index survives at its actual initial record. -/
theorem family_completed_cover_cut (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → ∃ i,
      Aux61GRec.completedCapture (S.marksData (cutSource S (family S))) i p := by
  filter_upwards [family_completed_cover S, family_ae_good S] with p hc hg hw
  obtain ⟨i, hi, hf, hs, y, hy, hl⟩ := hc hw
  have he : p ∈ (family S).event i := hi
  have hcut : p ∈ (cutSource S (family S)).event i := ⟨he, hg⟩
  have heq : inPath ((cutSource S (family S)).event i)
      (sourceChart (cutSource S (family S)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (family S)).path i) ((cutSource S (family S)).contact i) p =
    inPath ((family S).event i)
      (sourceChart (family S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family S).path i) ((family S).contact i) p := by
    funext v
    simp only [inPath, hcut, he, true_and]
    rfl
  refine ⟨i, hi, hf, ?_, y, hy, ?_⟩
  · intro v hv
    change inPath ((cutSource S (family S)).event i)
      (sourceChart (cutSource S (family S)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (family S)).path i) ((cutSource S (family S)).contact i) p v ∈
      ((cutSource S (family S)).data i).V
    rw [heq]
    exact hs v hv
  · change Tendsto (inPath ((cutSource S (family S)).event i)
      (sourceChart (cutSource S (family S)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (family S)).path i) ((cutSource S (family S)).contact i) p)
      (𝓝[<] ((cutSource S (family S)).contact i p).toNNReal) (𝓝 (y : ℂ))
    rw [heq]
    exact hl

end InteractingSLE.Sec5.Aux61GWindow18
