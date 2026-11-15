/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Match
import InteractingSLE.Spec.Sec5.Aux61CmpCover

/-! # The landed comparison API on the normalized refined source

The installed words have canonical seed heights. COMPARE's committed
collar theorem therefore applies with all restart and normalization
prerequisites proved. Its R101 access-selection input remains with COMPARE.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61GR1F Aux61Asm2 Aux61FibData LawUnique
universe u

/-- Both signed reference words have the canonical two seed heights. -/
theorem intervalWord_seed_heights (S : SourceSetting.{u}) (I : ReferenceInterval) :
    PiecewiseConstantBoundaryData.leftLim (intervalWord S I).boundary 0 = -sleLambda S.κ ∧
    PiecewiseConstantBoundaryData.rightLim (intervalWord S I).boundary 0 = sleLambda S.κ := by
  unfold intervalWord
  split_ifs with h
  · constructor
    · apply Sec4.leftLim_eq_of_forall (a := -1) (by norm_num)
      intro z hz
      change positiveBoundary _ _ _ _ z = _
      simp only [positiveBoundary, Aux61GPrime.negativeBoundary,
        ite_eq_left hz.2, ite_eq_left (hz.2.trans h.1),
        ite_eq_left (hz.2.trans (h.1.trans h.2)), sub_self, mul_zero, add_zero]
    · apply Sec4.rightLim_eq_of_forall h.1
      intro z hz
      change positiveBoundary _ _ _ _ z = _
      simp only [positiveBoundary, Aux61GPrime.negativeBoundary,
        ite_eq_right (not_lt.2 hz.1.le), ite_eq_left hz.2,
        ite_eq_left (hz.2.trans h.2), sub_self, mul_zero, add_zero]
  · have hn := I.2.resolve_left h
    constructor
    · apply Sec4.leftLim_eq_of_forall hn.2
      intro z hz
      exact Aux61GPrime.negativeBoundary_seedLeft hn.1 hz.1 hz.2
    · apply Sec4.rightLim_eq_of_forall (a := 1) (by norm_num)
      intro z hz
      exact Aux61GPrime.negativeBoundary_pos hn.1 hn.2 hz.1

/-- COMPARE's committed full-ball germ theorem for the exact canonical
cut family. All GLUEINST prerequisites are proved; the sole remaining
argument is the R101 access selection owned by COMPARE. This helper is
not an assertion that the seed/buffer-only restriction has that property. -/
theorem refinedFamily_pastGermCover_of_access (S : SourceSetting.{u})
    (haccess : ∀ i, ∀ᵐ p ∂S.μ,
      (S.marksData (cutSource S (withRecordPath S (refinedFamily S)))).Z i p ∈
        (S.marksData (cutSource S (withRecordPath S (refinedFamily S)))).B i →
      ∀ b ∈ ((S.marksData (cutSource S (withRecordPath S (refinedFamily S)))).data i).O₀,
        Aux61Cmp.OwnCollarPoint S (cutSource S (withRecordPath S (refinedFamily S))) i p b ∨
          Aux61Cmp.CounterGerm S (cutSource S (withRecordPath S (refinedFamily S))) i p b) :
    ∀ i, Aux61GChoice16.PastGermCover S (cutSource S (withRecordPath S (refinedFamily S))) i i.1.1.1 := by
  intro i
  apply Aux61Cmp.pastGermCover_of_access (refinedFamily_cut_restart S) i i.1.1.1 rfl
    (intervalWord_seed_heights S i.1.2.1).1 (intervalWord_seed_heights S i.1.2.1).2 _ (haccess i)
  filter_upwards [canonicalFamily_geometry (refinedChoices S) i] with p hp he
  exact hp he.1

end InteractingSLE.Sec5.Aux61GWindow17
