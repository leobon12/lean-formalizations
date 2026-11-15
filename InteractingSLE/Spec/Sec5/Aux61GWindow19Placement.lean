/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow18Cover

/-! # Seed-piece placement independent of the returned-word height

A per-outcome family may change its reference heights, real comparison
sets and selected access tests. Its seed and finite-buffer proofs depend
only on its retained time and placement inside a certified record piece.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61GInst Aux61FibData LawUnique
universe u
variable {S : SourceSetting.{u}}

/-- Structural placement of an arbitrary height-indexed choice family
inside the landed Borel seed and finite-buffer pieces. No conditional
mean, access cover or completed-capture assertion is part of placement. -/
structure SeedPlacement (C : RestartChoices S) where
  time : C.ι → Aux61GWindow17.GoodTime S
  window : C.ι → Aux61GWindow17.AllowedWindow
  time_eq : ∀ i, C.q i = (time i).1
  selected_sub : ∀ i, C.selected i ⊆ Aux61GWindow17.windowRecords S (time i) (window i)
  window_sub : ∀ i, (C.data i).V ⊆ seedExitWindow
    (basisBuffer (window i).1.1.1.1) ((window i).1.1.1.2.2 : ℝ)
  buffer_sub : ∀ i, closure (C.data i).buffer ⊆ closure (outerBuffer (window i).1.1)

/-- Exact equality with the normalized time chart for an arbitrary
family, with an independently supplied equal retained-time index. -/
theorem normalized_chart_eq_time (C : RestartChoices S) (i : C.Idx)
    (t : Aux61GWindow17.GoodTime S) (hq : C.q i.1 = t.1) :
    Aux61SlitWX.chart C.toR1Restart C.hasChart i = Aux61GWindow17.recordChart S t :=
  (Aux61GWindow18.normalized_chart_eq_recordChart C i).trans
    (Aux61GWindow17.recordChart_eq_of_time_eq S _ _ hq)

/-- Physical charts use the same retained record even when words and
record selections change. -/
theorem sourceChart_eq_time (C : RestartChoices S) (i : C.Idx)
    (t : Aux61GWindow17.GoodTime S) (hq : C.q i.1 = t.1) (p : S.Ω × HistorySpace 0 0) :
    sourceChart (Aux61SlitWX.source C.toR1Restart C.hasChart) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p = Aux61GWindow17.recordChart S t (C.record i.1 p) := by
  change Aux61SlitWX.chart C.toR1Restart C.hasChart i (C.record i.1 p) = _
  rw [normalized_chart_eq_time C i t hq]

namespace SeedPlacement
variable {C : RestartChoices S} (P : SeedPlacement C)
include P

/-- The finite restriction retains every record admitted by a placed
family, independently of its height, phase and access labels. -/
theorem selected_survives_finite (i : C.Idx) {y : SourceRecord S.nL S.nR}
    (hy : y ∈ C.toR1Restart.selected i) :
    y ∈ (Aux61SlitWAC.restrictChoices C (Aux61WndCap.finiteRestrict C)).toR1Restart.selected i := by
  have hw := P.selected_sub i.1 hy.1
  refine ⟨⟨hy.1, ?_⟩, hy.2⟩
  have he : Aux61WndCap.finiteRestrict C i.1 =
      Aux61WndCap.normFiniteRecords C i (C.data i.1).buffer := by
    unfold Aux61WndCap.finiteRestrict
    exact dite_eq_left i.2
  rw [he]
  refine ⟨⟨hy, hw.1.2⟩, ?_⟩
  rw [normalized_chart_eq_time C i (P.time i.1) (P.time_eq i.1)]
  intro z hz
  exact hw.2.1 z ⟨P.buffer_sub i.1 hz.1, hz.2⟩

/-- Placement guarantees exact equality of selected sets after the
finite restriction. This is a pointwise record statement. -/
theorem finite_selected_eq (i : C.Idx) :
    (Aux61SlitWAC.restrictChoices C (Aux61WndCap.finiteRestrict C)).toR1Restart.selected i =
      C.toR1Restart.selected i := by
  ext y
  exact ⟨fun hy => ⟨hy.1.1, hy.2⟩, P.selected_survives_finite i⟩

end SeedPlacement
end InteractingSLE.Sec5.Aux61GWindow19
