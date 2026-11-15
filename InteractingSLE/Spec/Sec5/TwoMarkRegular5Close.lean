/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkImage4Endpoint
import InteractingSLE.Spec.Restart.RetEndLimit
import InteractingSLE.Spec.Sec2.Assembly2Close

/-!
# Versions closed at a finite positive horizon

Only the value at a finite positive horizon is replaced by its left limit.
Values before the horizon and the initial value are preserved exactly.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Regular5

/-- Replace the value at a finite positive horizon by the left limit. -/
def endpointClose (T : ℝ≥0∞) (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if (t : ℝ≥0∞) = T ∧ t ≠ 0 then limUnder (𝓝[<] T.toNNReal) f else f t

/-- The initial value is preserved even when the horizon is zero. -/
theorem endpointClose_zero (T : ℝ≥0∞) (f : ℝ≥0 → ℝ) : endpointClose T f 0 = f 0 := by
  simp only [endpointClose, ne_eq, not_true_eq_false, and_false, ↓reduceIte]

/-- No value before the horizon changes. -/
theorem endpointClose_of_lt {T : ℝ≥0∞} {f : ℝ≥0 → ℝ} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : endpointClose T f t = f t := by
  simp only [endpointClose, ht.ne, false_and, ↓reduceIte]

/-- Closing a path preserves continuity before its horizon. -/
theorem continuousOn_endpointClose_before {T : ℝ≥0∞} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < T}) :
    ContinuousOn (endpointClose T f) {t : ℝ≥0 | (t : ℝ≥0∞) < T} :=
  hf.congr fun _ ht => endpointClose_of_lt ht

/-- A finite left limit makes the closed version continuous through its horizon. -/
theorem continuousOn_endpointClose {T : ℝ≥0∞} {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < T}) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) = T)
    (hlim : 0 < s → ∃ c : ℝ, Tendsto f (𝓝[<] s) (𝓝 c)) :
    ContinuousOn (endpointClose T f) (Iic s) := by
  intro t ht
  rcases (show t ≤ s from ht).lt_or_eq with hts | rfl
  · have htT : (t : ℝ≥0∞) < T := (ENNReal.coe_lt_coe.2 hts).trans_eq hs
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < T} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((continuousOn_endpointClose_before hf).continuousAt (hopen.mem_nhds htT)).continuousWithinAt
  · rcases eq_zero_or_pos t with rfl | ht0
    · exact continuousWithinAt_singleton.mono (by
        intro u hu
        exact mem_singleton_iff.2 (le_antisymm hu zero_le))
    · obtain ⟨c, hc⟩ := hlim ht0
      have : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
      have he : endpointClose T f t = c := by
        have hif : (t : ℝ≥0∞) = T ∧ t ≠ 0 := ⟨hs, ht0.ne'⟩
        unfold endpointClose
        split_ifs
        rw [← hs, ENNReal.toNNReal_coe, hc.limUnder_eq]
      rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, he]
      refine hc.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact (endpointClose_of_lt ((ENNReal.coe_lt_coe.2 hu).trans_eq hs)).symm

end InteractingSLE.Sec5.TwoMark.Regular5
