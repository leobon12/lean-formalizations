/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow19Thin

/-! # Transfer actual access captures to arbitrary per-outcome words

Only equality of retained times, membership of the actual initial record,
window containment and the endpoint's reference interval are needed.
Neither the selected word height nor the shape of O₀ enters this proof.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61GInst Aux61FibData LawUnique
universe u
variable {S : SourceSetting.{u}}

/-- Actual initial records depend only on the retained rational time. -/
theorem record_eq_time (C : RestartChoices S) (i : C.Idx)
    (t : Aux61GWindow17.GoodTime S) (hq : C.q i.1 = t.1) (p : S.Ω × HistorySpace 0 0) :
    C.record i.1 p = timeRecord S t p := by
  change (_, Aux61ULoc.stopRec (rationalTime (C.q i.1)) _) =
    (_, Aux61ULoc.stopRec (rationalTime t.1) _)
  rw [hq]

/-- The time-source path is the fully normalized base-model path. -/
theorem timePath_eq_normalized (t : Aux61GWindow17.GoodTime S) (p : S.Ω × HistorySpace 0 0) :
    timePath S t p =
      inPath ((Aux61SlitWX.source (Aux61GWindow17.baseChoices S t.1).toR1Restart
          (Aux61GWindow17.baseChoices S t.1).hasChart).event (timeIndex S t))
        (sourceChart (Aux61SlitWX.source (Aux61GWindow17.baseChoices S t.1).toR1Restart
          (Aux61GWindow17.baseChoices S t.1).hasChart) (rationalTime S.s)
          S.own.W S.own.VL S.own.VR S.life (timeIndex S t))
        ((timeSource S t).path (timeIndex S t)) (timeContact S t) p := by
  funext v
  unfold timePath inPath
  rw [sourceChart_eq_time (Aux61GWindow17.baseChoices S t.1) (timeIndex S t) t rfl p]
  rfl

namespace SeedPlacement
variable {C : RestartChoices S} (P : SeedPlacement C)
include P

/-- On an admitted actual record the entire selected normalized path is
the time-source access, also after the finite restriction. -/
theorem inPath_eq_time (i : C.Idx) (t : Aux61GWindow17.GoodTime S) (hq : C.q i.1 = t.1)
    {p : S.Ω × HistorySpace 0 0} (hp : C.record i.1 p ∈ C.toR1Restart.selected i) :
    inPath ((family C).event i)
      (sourceChart (family C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family C).path i) ((family C).contact i) p = timePath S t p := by
  have hfinite := P.selected_survives_finite i hp
  have hb : p ∈ (Aux61GWindow17.baseChoices S t.1).fam.event (timeIndex S t) := by
    refine ⟨mem_univ _, ?_⟩
    have hg := hp.2
    change C.record i.1 p ∈ goodSet (rationalTime S.s) (C.q i.1) at hg
    rw [record_eq_time C i t hq p, hq] at hg
    exact hg
  exact (Aux61SlitWAC.normalized_inPath_eq_of_time_eq (finiteChoices C)
    (Aux61GWindow17.baseChoices S t.1) i (timeIndex S t) hq hfinite hb).trans
    (timePath_eq_normalized t p).symm

/-- A geometrically capturing window and an admitted initial record give
a completed capture for any installed height and landing reference. -/
theorem completedCapture_of_time_capture (i : C.Idx) (t : Aux61GWindow17.GoodTime S)
    (hq : C.q i.1 = t.1) {p : S.Ω × HistorySpace 0 0}
    (hp : C.record i.1 p ∈ C.toR1Restart.selected i)
    (hfin : timeContact S t p < ⊤) (J : Aux61GWindow17.AllowedWindow)
    (hstay : ∀ v : ℝ≥0, (v : ℝ≥0∞) < timeContact S t p → timePath S t p v ∈ bufferedWindow J.1.1)
    {y : ℝ} (hend : Tendsto (timePath S t p)
      (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)))
    (hV : bufferedWindow J.1.1 ⊆ (C.data i.1).V) (hI : y ∈ Ioo (C.left i.1) (C.right i.1)) :
    Aux61GRec.completedCapture (S.marksData (family C)) i p := by
  have hT : (family C).contact i p = timeContact S t p := congrFun
    (Aux61SlitWAC.contact_eq_of_time_eq (finiteChoices C) (Aux61GWindow17.baseChoices S t.1)
      i (timeIndex S t) hq) p
  have heq := P.inPath_eq_time i t hq hp
  have hf : (family C).contact i p < ⊤ := by rw [hT]; exact hfin
  refine ⟨P.selected_survives_finite i hp, hf, ?_, y, hI, ?_⟩
  · intro v hv
    change inPath ((family C).event i)
      (sourceChart (family C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family C).path i) ((family C).contact i) p v ∈ (C.data i.1).V
    rw [heq]
    have hv' : (v : ℝ≥0∞) < timeContact S t p := by
      change (v : ℝ≥0∞) < (family C).contact i p at hv
      rwa [hT] at hv
    exact hV (hstay v hv')
  · change Tendsto (inPath ((family C).event i)
      (sourceChart (family C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((family C).path i) ((family C).contact i) p)
      (𝓝[<] ((family C).contact i p).toNNReal) (𝓝 (y : ℂ))
    rw [heq, hT]
    exact hend

end SeedPlacement
end InteractingSLE.Sec5.Aux61GWindow19
