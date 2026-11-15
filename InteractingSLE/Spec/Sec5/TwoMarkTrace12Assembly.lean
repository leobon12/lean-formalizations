/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkTrace12Avoid
import InteractingSLE.Spec.Sec5.Aux65NegReference

/-!
# The stopped two-mark theorem and the negative R5 reference

The two-mark exclusion is proved from the announced local evolution and its
given injective trace. The existing negative-reference reduction then supplies
R5 without any additional mathematical input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.TwoMark.Trace12

/-- The stopped low-weight two-mark exclusion, including the terminal stop. -/
theorem twoMarkLowUpToStatement : Aux65Neg.TwoMarkLowUpToStatement.{u} := by
  intro κ a b r hκ hκ4 ha hab hr Ω mΩ P hP 𝓕 W B xL ρL VL VR e hE _hW _hVR A hA η hη hinj
  exact ae_avoid_interval hκ hκ4 ha hab hr hE hA hη hinj

/-- The negative-side R5 reference statement follows from the proved stopped two-mark theorem. -/
theorem r5NegStatement : Aux61Cov.R5NegStatement.{u} :=
  Aux65Neg.r5NegStatement_of_twoMarkLowUpTo twoMarkLowUpToStatement

end InteractingSLE.Sec5.TwoMark.Trace12
