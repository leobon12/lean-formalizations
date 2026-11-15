/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntExtendUnion

/-!
# Every constructed retained prefix pair has a proper inverse extension

The individual prefix extensions and raw filling identities were proved
from run regularity. The filled union theorem now discharges the properness
field left open in the preceding retained boundary family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntExtend

open WalkIntCanon WalkIntFill

/-- Properness of the joint retained chart is a theorem for every selected
pair, rather than additional physical boundary geometry. -/
theorem hasProperBdryExt_retainedPair {sR sL : ExplState} (J : RetainedPair sR sL) :
    GW1P.HasProperBdryExt J.chart := by
  have hR : fillH J.right.raw = J.right.model.hull := J.right.filled.symm
  have hL : fillH J.left.raw = J.left.model.hull := J.left.filled.symm
  have hM : J.model.hull = fillH (J.right.model.hull ∪ J.left.model.hull) := by
    rw [J.filled, ← hR, ← hL]
    exact (fillH_union_filled J.right.raw_subset_H J.left.raw_subset_H
      (hR.symm ▸ J.right.model.isHull) (hL.symm ▸ J.left.model.isHull)).symm
  exact hasProperBdryExt_of_filled_union J.right.model J.left.model J.model
    J.right.normalized.conformal J.left.normalized.conformal J.right.proper J.left.proper
    J.normalized.conformal J.normalized.inverse_bound hM

end InteractingSLE.Theorem14.WalkIntExtend
