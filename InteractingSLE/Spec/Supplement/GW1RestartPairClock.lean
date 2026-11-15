/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPairChart

/-!
# BW1–BW2: composing clocks in the current physical chart

The original chart in `GW1LaunchClock.IsPrefixClock` is fixed to the initial
inversion. Here both charts are arbitrary: BW1 takes place inside a later
conditional domain. The finite connector cut is an attained first visit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1RestartPair

/-- A complete relative curve is the source curve before its first visit to the
retained set, in arbitrary physical charts. -/
def IsRetainedClock (source target : Chart) (W V : ℝ≥0 → ℝ)
    (A : Set ℂ) (b : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous b ∧ StrictMono b ∧
    range b = {s : ℝ≥0 | (s : ℝ≥0∞) < firstTipTime source W A} ∧
    ∀ r z, target.tipAt V r z ↔ source.tipAt W (b r) z

/-- An attained finite contact in the relative clock is the first contact in
the source clock. This works for the whole newly retained set. -/
theorem firstTipTime_eq_of_retainedClock {source target : Chart}
    {W V : ℝ≥0 → ℝ} {A B : Set ℂ} {b : ℝ≥0 → ℝ≥0}
    (h : IsRetainedClock source target W V A b) {T : ℝ≥0}
    (hT : firstTipTime target V B = T) (hhit : ∃ z ∈ B, target.tipAt V T z) :
    firstTipTime source W B = b T := by
  have hbT : (b T : ℝ≥0∞) < firstTipTime source W A := by
    have hm := mem_range_self (f := b) T
    rw [h.2.2.1] at hm
    exact hm
  apply le_antisymm
  · obtain ⟨z, hz, ht⟩ := hhit
    exact iInf₂_le (b T) ⟨z, hz, (h.2.2.2 T z).1 ht⟩
  · refine le_iInf fun t => le_iInf fun ht => ?_
    by_cases hle : b T ≤ t
    · exact ENNReal.coe_le_coe.2 hle
    have htℓ : t < b T := lt_of_not_ge hle
    have htR : t ∈ range b := by
      rw [h.2.2.1]
      exact (ENNReal.coe_lt_coe.2 htℓ).trans hbT
    obtain ⟨r, hr⟩ := htR
    obtain ⟨z, hz, htip⟩ := ht
    have hrT : r < T := h.2.1.lt_iff_lt.1 (by rw [hr]; exact htℓ)
    have hVr : target.tipAt V r z := (h.2.2.2 r z).2 (by rw [hr]; exact htip)
    have hTr : (T : ℝ≥0∞) ≤ r := hT ▸ (iInf₂_le r ⟨z, hz, hVr⟩)
    exact False.elim ((not_le.2 hrT) (ENNReal.coe_le_coe.1 hTr))

/-- Compose a terminal-prefix clock with a finite retargeting clock. -/
theorem IsRetainedClock.compose_cut {source target next : Chart}
    {W V U : ℝ≥0 → ℝ} {A B : Set ℂ} {b a : ℝ≥0 → ℝ≥0}
    (h : IsRetainedClock source target W V A b) {T : ℝ≥0}
    (hT : firstTipTime target V B = T) (hhit : ∃ z ∈ B, target.tipAt V T z)
    (ha : Continuous a) (ham : StrictMono a) (har : range a = Iio T)
    (hid : ∀ r z, next.tipAt U r z ↔ target.tipAt V (a r) z) :
    IsRetainedClock source next W U B (b ∘ a) := by
  refine ⟨h.1.comp ha, h.2.1.comp ham, ?_, fun r z =>
    (hid r z).trans (h.2.2.2 (a r) z)⟩
  rw [range_comp, har, GW1LaunchClock.image_initial_segment h.2.1 h.2.2.1,
    firstTipTime_eq_of_retainedClock h hT hhit]
  ext s
  simp only [mem_Iio, mem_ofPred_eq, ENNReal.coe_lt_coe]

end InteractingSLE.Theorem14.GW1RestartPair
