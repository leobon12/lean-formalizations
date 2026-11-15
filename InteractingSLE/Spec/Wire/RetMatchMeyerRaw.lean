/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchGalFinish

/-!
# Removing killing from a raw canonical stopping time

A raw history stopping time can be read on complete state paths by recording
an infinite history. Before a killed record ends, this changes no stopping
value. Together with the existing strict-past reader and Galmarino test, this
provides the entire deterministic step needed after predictable-time lifting.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchMeyer

open LawUnique Restart.FlowStopIdentG RetMatchRaw RetMatchGal

variable {nL nR : ℕ}

/-- Record every dyadic sample of a complete state path. -/
def fullHistory (w : ℝ≥0 → DrivingValue nL nR) : HistorySpace nL nR :=
  (⊤, fun p => w (dyadicTime p))

theorem measurable_fullHistory : Measurable (fullHistory (nL := nL) (nR := nR)) :=
  measurable_const.prodMk (measurable_pi_iff.2 fun p => measurable_pi_apply (dyadicTime p))

/-- Coordinate evaluation at a past time is measurable in the raw path filtration. -/
theorem measurable_statePath_eval {r t : ℝ≥0} (hr : r ≤ t) :
    Measurable[statePathFiltration t] (fun w : ℝ≥0 → DrivingValue nL nR => w r) := by
  apply Measurable.of_comap_le
  exact (le_iSup_of_le r (le_iSup_of_le hr le_rfl))

/-- Infinite recording respects the raw filtrations, on arbitrary state paths. -/
theorem measurable_fullHistory_at (t : ℝ≥0) :
    Measurable[statePathFiltration t, historyFiltration t]
      (fullHistory (nL := nL) (nR := nR)) := by
  let : MeasurableSpace (ℝ≥0 → DrivingValue nL nR) := statePathFiltration t
  intro A hA
  change MeasurableSet[MeasurableSpace.generateFrom _] A at hA
  refine MeasurableSpace.generateFrom_induction _
    (fun E _ => MeasurableSet[statePathFiltration t] (fullHistory ⁻¹' E))
    ?_ ?_ ?_ ?_ A hA
  · rintro E ⟨r, hrt, B, hB, rfl⟩ _
    have hm : Measurable[statePathFiltration t]
        (fun w : ℝ≥0 → DrivingValue nL nR => histState (fullHistory w) r) := by
      unfold histState fullHistory
      exact (StronglyMeasurable.limUnder fun k =>
        (measurable_statePath_eval
          ((dyadicTime_lowerDyadic_le r k).trans hrt)).stronglyMeasurable).measurable
    convert hm hB using 1
    ext w
    simp only [mem_preimage, mem_ofPred_eq, fullHistory, ENNReal.coe_lt_top, true_and]
  · exact MeasurableSet.empty
  · intro E _ hE
    exact hE.compl
  · intro E _ hE
    simpa only [preimage_iUnion] using MeasurableSet.iUnion hE

/-- A raw canonical stop therefore gives a raw stop on complete state paths. -/
theorem isStoppingTime_fullHistory {τ : HistorySpace nL nR → ℝ≥0∞}
    (hτ : IsStoppingTime historyFiltration (fun γ => (τ γ : WithTop ℝ≥0))) :
    IsStoppingTime statePathFiltration (fun w => (τ (fullHistory w) : WithTop ℝ≥0)) :=
  fun t => measurable_fullHistory_at t (hτ t)

/-- Raw history events agree on two records that are alive through the same
closed prefix and have the same state on that prefix. -/
theorem mem_iff_of_history_prefix {t : ℝ≥0} {A : Set (HistorySpace nL nR)}
    (hA : MeasurableSet[historyFiltration t] A) {γ δ : HistorySpace nL nR}
    (hγ : (t : ℝ≥0∞) < γ.1) (hδ : (t : ℝ≥0∞) < δ.1)
    (hag : ∀ r ≤ t, histState γ r = histState δ r) : γ ∈ A ↔ δ ∈ A := by
  change MeasurableSet[MeasurableSpace.generateFrom _] A at hA
  refine MeasurableSpace.generateFrom_induction _ (fun E _ => γ ∈ E ↔ δ ∈ E)
    ?_ ?_ ?_ ?_ A hA
  · rintro E ⟨r, hrt, B, _, rfl⟩ _
    have hrγ := (ENNReal.coe_le_coe.2 hrt).trans_lt hγ
    have hrδ := (ENNReal.coe_le_coe.2 hrt).trans_lt hδ
    change (↑r < γ.1 ∧ histState γ r ∈ B) ↔ (↑r < δ.1 ∧ histState δ r ∈ B)
    rw [hag r hrt]
    exact and_congr (iff_of_true hrγ hrδ) Iff.rfl
  · exact Iff.rfl
  · intro E _ hE
    exact not_congr hE
  · intro E _ hE
    simp only [mem_iUnion]
    exact exists_congr hE

/-- A raw stopping value strictly before both record ends is fixed by its
closed state prefix. No probabilistic hypothesis occurs in this test. -/
theorem eq_of_isStoppingTime_historyPrefix {τ : HistorySpace nL nR → ℝ≥0∞}
    (hτ : IsStoppingTime historyFiltration (fun γ => (τ γ : WithTop ℝ≥0)))
    (γ δ : HistorySpace nL nR) (hγ : τ γ < γ.1) (hδ : τ γ < δ.1)
    (hag : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ τ γ → histState γ r = histState δ r) :
    τ δ = τ γ := by
  have transfer : ∀ {a b : HistorySpace nL nR} {t : ℝ≥0},
      (t : ℝ≥0∞) < a.1 → (t : ℝ≥0∞) < b.1 →
      (∀ r ≤ t, histState a r = histState b r) → τ a ≤ (t : ℝ≥0∞) → τ b ≤ t := by
    intro a b t ha hb hp ht
    exact (mem_iff_of_history_prefix (hτ t) ha hb hp).1 ht
  apply le_antisymm
  · by_contra hn
    have hlt : τ γ < τ δ := not_le.1 hn
    let t := (τ γ).toNNReal
    have ht : τ γ = (t : ℝ≥0∞) := (ENNReal.coe_toNNReal (ne_top_of_lt hlt)).symm
    have hle : τ δ ≤ (t : ℝ≥0∞) := transfer (ht ▸ hγ) (ht ▸ hδ)
      (fun r hr => hag r ((ENNReal.coe_le_coe.2 hr).trans_eq ht.symm)) ht.le
    exact (not_le_of_gt hlt) (hle.trans_eq ht.symm)
  · by_contra hn
    have hlt : τ δ < τ γ := not_le.1 hn
    let t := (τ δ).toNNReal
    have ht : τ δ = (t : ℝ≥0∞) := (ENNReal.coe_toNNReal (ne_top_of_lt hlt)).symm
    have htγ : (t : ℝ≥0∞) < τ γ := ht ▸ hlt
    have hle : τ γ ≤ (t : ℝ≥0∞) := transfer (htγ.trans hδ) (htγ.trans hγ)
      (fun r hr => (hag r ((ENNReal.coe_le_coe.2 hr).trans htγ.le)).symm) ht.le
    exact (not_le_of_gt hlt) (hle.trans_eq ht.symm)

end InteractingSLE.Wire.RetMatchMeyer
