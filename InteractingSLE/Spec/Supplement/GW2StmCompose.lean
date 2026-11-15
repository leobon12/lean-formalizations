/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaunchClockCompose

/-!
# GW2's stage step, part 8: composing launch clocks when the new piece may never be met

Packet PROVE-GW2-STAGEMEAN, step round (`GW2SchedRule.GB6StagedEqStepStatement`). GW1's clock composition
(`GW1LaunchClock.IsPrefixClock.compose_cut`) adds to the retained union a set `B` that the relative counterflow meets
at a finite attained time. At a GW2 launch the relative clock of GB6 runs up to the first contact `T_c ∈ [0, ∞]` of the
conditional counterflow with the new piece; this file allows `T_c = ∞`:

* **`IsPrefixClock.compose_cut_top`**: `compose_cut` with `T : ℝ≥0∞`, the hit required only when `T` is finite; when
  `T = ∞` the relative counterflow never meets `B`, so the original one does not meet it before leaving the old
  clock's range, and the first visit of `A ∪ B` is that of `A`.

Deterministic. Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Stm

open GW1LaunchClock

/-- **Clock composition with a possibly infinite contact time.** -/
theorem IsPrefixClock.compose_cut_top {c d : Chart} {W V U : ℝ≥0 → ℝ} {A B : Set ℂ} {ℓ a : ℝ≥0 → ℝ≥0}
    (h : IsPrefixClock c W V A ℓ) {T : ℝ≥0∞}
    (hT : firstTipTime (c.trans infinitySourceChart) V B = T)
    (hhit : ∀ T' : ℝ≥0, (T' : ℝ≥0∞) = T → ∃ z ∈ B, (c.trans infinitySourceChart).tipAt V T' z)
    (ha : Continuous a) (ham : StrictMono a) (har : range a = {t : ℝ≥0 | (t : ℝ≥0∞) < T})
    (hid : ∀ r z, (d.trans infinitySourceChart).tipAt U r z ↔ (c.trans infinitySourceChart).tipAt V (a r) z) :
    IsPrefixClock d W U (A ∪ B) (ℓ ∘ a) := by
  rcases eq_or_ne T ⊤ with hTt | hTt
  · refine ⟨h.1.comp ha, h.2.1.comp ham, ?_, fun r z => (hid r z).trans (h.2.2.2 (a r) z)⟩
    have hau : range a = univ := by
      rw [har, hTt]
      ext t
      simp only [ENNReal.coe_lt_top, ofPred_true, mem_univ]
    have hfirst : firstTipTime infinitySourceChart W (A ∪ B) = firstTipTime infinitySourceChart W A := by
      refine le_antisymm (firstTipTime_mono subset_union_left) (le_iInf fun t => le_iInf fun ht => ?_)
      refine le_of_not_gt fun htA => ?_
      obtain ⟨z, hzA | hzB, htip⟩ := ht
      · exact (not_le.2 htA) (iInf₂_le t ⟨z, hzA, htip⟩)
      · have htR : t ∈ range ℓ := by rw [h.2.2.1]; exact htA
        obtain ⟨r, rfl⟩ := htR
        have hVr : (c.trans infinitySourceChart).tipAt V r z := (h.2.2.2 r z).2 htip
        have h1 : firstTipTime (c.trans infinitySourceChart) V B ≤ r := iInf₂_le r ⟨z, hzB, hVr⟩
        rw [hT, hTt] at h1
        exact (not_le.2 ENNReal.coe_lt_top) h1
    rw [range_comp, hau, image_univ, h.2.2.1, hfirst]
  · obtain ⟨T', rfl⟩ := WithTop.ne_top_iff_exists.1 hTt
    have har' : range a = Iio T' := by
      rw [har]
      ext t
      simp only [mem_ofPred_eq, mem_Iio]
      exact ENNReal.coe_lt_coe
    exact h.compose_cut hT (hhit T' rfl) ha ham har' hid

end InteractingSLE.Theorem14.GW2Stm
