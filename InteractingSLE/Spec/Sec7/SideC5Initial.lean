/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Data

/-!
# The actual interior-visit event is empty at capacity zero

PROVE-SIDE-COLLAR2 continuation. Ready makes every interior original visit
have strictly positive relative capacity. Thus this reference event cannot
supply the initial collar; the initial slice is a separate obligation.
-/

set_option autoImplicit false
noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

/-- No actual interior visit is earlier than relative capacity zero.
This is why the positive-time height cover does not assert its initial slice. -/
theorem referenceVisitEvent_zero_eq_empty {Ω : Type} [MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (s : ℝ≥0) : j.referenceVisitEvent i d s 0 = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  rintro ω ⟨hA, _, hVisit, hOrder, _⟩
  have hpos := (visitCapacity_spec hj hA s.coe_nonneg hVisit).1
  have hpos' : 0 < (j.visitCapacity d ω s).toNNReal := Real.toNNReal_pos.2 hpos
  exact (not_lt_of_ge hOrder) hpos'

end InteractingSLE.Wire.Current.SideTest
