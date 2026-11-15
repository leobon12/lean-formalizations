/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetGeometry
import InteractingSLE.Spec.Sec5.Lemma57Cap

/-! # Deterministic Q-clock adapters for Lemma 5.7

A pulled-back Q prefix keeps its own clock. Freezing at its terminal point
supplies the global interior-path hypothesis of the existing capacity adapter.
Order is also preserved under any increasing change of the prefix clock.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Wire
open QuantumZipper Sec4 Prop513Target Prop513Schedule

/-- A Q prefix pulled back to E, extended constantly past its terminal time. -/
def pullPrefix (q T : ℝ) (η : ℝ → ℂ) (t : ℝ) : ℂ :=
  (targetChart q).2.1 (η (min (max t 0) T))

theorem pullPrefix_of_mem (q : ℝ) {T t : ℝ} (η : ℝ → ℂ) (ht : t ∈ Icc 0 T) :
    pullPrefix q T η t = (targetChart q).2.1 (η t) := by
  rw [pullPrefix, max_eq_left ht.1, min_eq_left ht.2]

theorem targetChart_inv_zero (q : ℝ) : (targetChart q).2.1 0 = 0 := by
  have he := inv_ofReal q 0
  norm_num [realInv] at he
  convert he using 1
  ring

theorem pullPrefix_zero (q : ℝ) {T : ℝ} (hT : 0 ≤ T) {η : ℝ → ℂ} (hη : η 0 = 0) :
    pullPrefix q T η 0 = 0 := by
  rw [pullPrefix_of_mem q η ⟨le_rfl, hT⟩, hη, targetChart_inv_zero]

theorem pullPrefix_mem_H {q T : ℝ} (hq : 0 < q) (hT : 0 < T) {η : ℝ → ℂ}
    (hη : ∀ t : ℝ, 0 < t → t ≤ T → η t ∈ H) :
    ∀ t : ℝ, 0 < t → pullPrefix q T η t ∈ H := by
  intro t ht
  apply (targetChart_isConformal hq).2.1
  apply hη
  · exact lt_min ((lt_of_lt_of_le ht (le_max_left _ _))) hT
  · exact min_le_right _ _

/-- On each positive-time prefix point, the two chart changes reduce to R. -/
theorem pullPrefix_capacity {q T t : ℝ} (hq : 0 < q) {η : ℝ → ℂ}
    (hη : ∀ r : ℝ, 0 < r → r ≤ T → η r ∈ H) (ht : 0 < t) (hT : t ≤ T) :
    (stripCounterflowChart q).1 (pullPrefix q T η t) = infinitySourceChart.1 (η t) := by
  rw [pullPrefix_of_mem q η ⟨ht.le, hT⟩]
  exact capacity_chart_of_target hq (hη t ht hT)

/-- The E-chart reverse-visit law of a pulled-back Q prefix gives its exact
capacity-chart geometry, including strictly positive counterflow visit times. -/
theorem target_reverseVisit_of_pullback {q T : ℝ} (hq : 0 < q) (hT : 0 < T)
    {γ : ℝ≥0 → ℂ} {η : ℝ → ℂ} (hγ0 : γ 0 = 0)
    (hγH : ∀ t : ℝ≥0, 0 < t → γ t ∈ H) (hη0 : η 0 = 0)
    (hηH : ∀ t : ℝ, 0 < t → t ≤ T → η t ∈ H)
    (hR : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
      ∃ u ∈ Icc (0 : ℝ) 1, stripCounterflowPath q γ u = pullPrefix q T η t ∧
        ∀ r ∈ Icc (0 : ℝ) u, stripCounterflowPath q γ r ≠ pullPrefix q T η s)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ T) :
    ∃ v : ℝ≥0, 0 < v ∧ γ v = infinitySourceChart.1 (η t) ∧
      ∀ w ≤ v, γ w ≠ infinitySourceChart.1 (η s) := by
  obtain ⟨v, hv, hbefore⟩ := lemma57_reverseOrder_capacityChart hq hγ0 hγH
    (pullPrefix_zero q hT.le hη0) (pullPrefix_mem_H hq hT hηH) hR hs.le hst ht
  rw [pullPrefix_capacity hq hηH (hs.trans hst) ht] at hv
  have hne : infinitySourceChart.1 (η t) ≠ 0 :=
    DerivLog.ne_zero_of_mem_H (Chart.isConformal_infinitySourceChart.2.1 (hηH t (hs.trans hst) ht))
  refine ⟨v, ?_, hv, ?_⟩
  · exact lt_of_le_of_ne zero_le (fun he => hne (by rw [← hv, ← he, hγ0]))
  · rwa [pullPrefix_capacity hq hηH hs (hst.le.trans ht)] at hbefore

/-- Reverse chronological visits are preserved by an increasing clock on the
prefix interval. This also applies samplewise to random capacity clocks. -/
theorem reverseVisit_comp_clock {T U : ℝ} {ξ η : ℝ → ℂ} {a : ℝ → ℝ}
    (ha : StrictMonoOn a (Icc 0 T)) (ham : MapsTo a (Icc 0 T) (Icc 0 U))
    (hR : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ U →
      ∃ u ∈ Icc (0 : ℝ) 1, ξ u = η t ∧ ∀ r ∈ Icc (0 : ℝ) u, ξ r ≠ η s) :
    ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
      ∃ u ∈ Icc (0 : ℝ) 1, ξ u = η (a t) ∧ ∀ r ∈ Icc (0 : ℝ) u, ξ r ≠ η (a s) := by
  intro s t hs hst ht
  have hsI : s ∈ Icc 0 T := ⟨hs, hst.le.trans ht⟩
  have htI : t ∈ Icc 0 T := ⟨hs.trans hst.le, ht⟩
  exact hR (a s) (a t) (ham hsI).1 (ha hsI htI hst) (ham htI).2

end InteractingSLE.Sec5.Prop513Wire
