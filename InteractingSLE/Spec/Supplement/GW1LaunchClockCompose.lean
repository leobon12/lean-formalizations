/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaunchClockBase

/-!
# GW1: composition of precontact clocks through an attained finite cut

The cut is the first visit to the entire newly retained set. The proof uses that
first visit directly; it takes no limit of first visits to proper subprefixes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1LaunchClock

/-- The pathwise part of a launch clock: the relative curve is precisely the
original precontact curve, with its actual increasing capacity parametrization. -/
def IsPrefixClock (c : Chart) (W V : ℝ≥0 → ℝ) (A : Set ℂ) (ℓ : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous ℓ ∧ StrictMono ℓ ∧
    range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime infinitySourceChart W A} ∧
    ∀ r z, (c.trans infinitySourceChart).tipAt V r z ↔
      infinitySourceChart.tipAt W (ℓ r) z

theorem image_initial_segment {ℓ : ℝ≥0 → ℝ≥0} {S : ℝ≥0∞}
    (hm : StrictMono ℓ) (hr : range ℓ = {s : ℝ≥0 | (s : ℝ≥0∞) < S}) (T : ℝ≥0) :
    ℓ '' Iio T = Iio (ℓ T) := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact hm ht
  · intro hs
    have hT : (ℓ T : ℝ≥0∞) < S := by
      have hm := mem_range_self (f := ℓ) T
      rw [hr] at hm
      exact hm
    have hsS : (s : ℝ≥0∞) < S := (ENNReal.coe_lt_coe.2 hs).trans hT
    have hsR : s ∈ range ℓ := by rw [hr]; exact hsS
    obtain ⟨t, rfl⟩ := hsR
    exact ⟨t, hm.lt_iff_lt.1 hs, rfl⟩

/-- The original first visit to the enlarged union is the old clock of the
attained relative first visit to the new set. Older raw pieces remain in the union. -/
theorem firstTipTime_union_eq {c : Chart} {W V : ℝ≥0 → ℝ} {A B : Set ℂ}
    {ℓ : ℝ≥0 → ℝ≥0} (h : IsPrefixClock c W V A ℓ) {T : ℝ≥0}
    (hT : firstTipTime (c.trans infinitySourceChart) V B = T)
    (hhit : ∃ z ∈ B, (c.trans infinitySourceChart).tipAt V T z) :
    firstTipTime infinitySourceChart W (A ∪ B) = ℓ T := by
  have hℓT : (ℓ T : ℝ≥0∞) < firstTipTime infinitySourceChart W A := by
    have hm := mem_range_self (f := ℓ) T
    rw [h.2.2.1] at hm
    exact hm
  apply le_antisymm
  · obtain ⟨z, hz, ht⟩ := hhit
    exact iInf₂_le (ℓ T) ⟨z, Or.inr hz, (h.2.2.2 T z).1 ht⟩
  · refine le_iInf fun t => le_iInf fun ht => ?_
    by_cases hle : ℓ T ≤ t
    · exact ENNReal.coe_le_coe.2 hle
    have htℓ : t < ℓ T := lt_of_not_ge hle
    have htA := (ENNReal.coe_lt_coe.2 htℓ).trans hℓT
    obtain ⟨z, hzA | hzB, htip⟩ := ht
    · exact False.elim ((not_le.2 htA) (iInf₂_le t ⟨z, hzA, htip⟩))
    · have htR : t ∈ range ℓ := by rw [h.2.2.1]; exact htA
      obtain ⟨r, hr⟩ := htR
      have hrT : r < T := h.2.1.lt_iff_lt.1 (by rw [hr]; exact htℓ)
      have hVr : (c.trans infinitySourceChart).tipAt V r z :=
        (h.2.2.2 r z).2 (by rw [hr]; exact htip)
      have hTr : (T : ℝ≥0∞) ≤ r := hT ▸ (iInf₂_le r ⟨z, hzB, hVr⟩)
      exact False.elim ((not_le.2 hrT) (ENNReal.coe_le_coe.1 hTr))

/-- Compose the old launch clock with the terminal/connector clock supplied in
that conditional world. The new clock stops at the whole enlarged retained union. -/
theorem IsPrefixClock.compose_cut {c d : Chart} {W V U : ℝ≥0 → ℝ} {A B : Set ℂ}
    {ℓ a : ℝ≥0 → ℝ≥0} (h : IsPrefixClock c W V A ℓ) {T : ℝ≥0}
    (hT : firstTipTime (c.trans infinitySourceChart) V B = T)
    (hhit : ∃ z ∈ B, (c.trans infinitySourceChart).tipAt V T z)
    (ha : Continuous a) (ham : StrictMono a) (har : range a = Iio T)
    (hid : ∀ r z, (d.trans infinitySourceChart).tipAt U r z ↔
      (c.trans infinitySourceChart).tipAt V (a r) z) :
    IsPrefixClock d W U (A ∪ B) (ℓ ∘ a) := by
  refine ⟨h.1.comp ha, h.2.1.comp ham, ?_, fun r z => (hid r z).trans (h.2.2.2 (a r) z)⟩
  rw [range_comp, har, image_initial_segment h.2.1 h.2.2.1,
    firstTipTime_union_eq h hT hhit]
  ext s
  simp only [mem_Iio, mem_ofPred_eq, ENNReal.coe_lt_coe]

end InteractingSLE.Theorem14.GW1LaunchClock
