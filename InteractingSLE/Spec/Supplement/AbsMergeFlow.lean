/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AbsMergeFixed
import InteractingSLE.Spec.Supplement.GW2aForceFlow

/-!
# `FixedTimeAbsorbedMergeStatement` proved; `FlowFixedTimeInteriorStatement` from Theorem 1.3 alone

Packet PROVE-ABSMERGE.

* **`GW2aForce.fixedTimeAbsorbedMergeStatement`**: PROVE-GW2A-FORCE's named input holds. An absorbed merge at `t` puts
  a force point on the driver at `t`, and by `AbsMerge.ae_forall_ne_of_isIntegratedSLEEvolution` (no force collision
  at a fixed time, for every `κ > 0`) this has probability `0`.
* **`GW2aForce.flowFixedTimeInteriorStatement_of_thm13`**: `GW2aStep.FlowFixedTimeInteriorStatement` from
  Theorem 1.3 alone (`flowFixedTimeInteriorStatement_of_absorbedMerge` with the input discharged). Ruling R48: this
  uses Theorem 1.3, so it serves Theorem 1.4, not the inputs of Theorems 1.2–1.3; the collision statements of
  `AbsMergeFixed` use only Definition 2.1 and may be used anywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aForce

/-- **`FixedTimeAbsorbedMergeStatement` holds**: at a deterministic time an absorbed merge almost surely does not
occur (indeed no force point is on the driver, `AbsMerge.ae_forall_ne_of_isIntegratedSLEEvolution`). -/
theorem fixedTimeAbsorbedMergeStatement : FixedTimeAbsorbedMergeStatement.{u} := by
  intro κ hκ _ nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ hE t ht
  filter_upwards [AbsMerge.ae_forall_ne_of_isIntegratedSLEEvolution hκ hF hE ht] with ω h htζ
  exact ⟨fun ⟨_, k', _, _, hcol, _⟩ => (h htζ).2 k' hcol.symm,
    fun ⟨_, k', _, _, hcol, _⟩ => (h htζ).1 k' hcol.symm⟩

/-- **`FlowFixedTimeInteriorStatement` from Theorem 1.3 alone.** -/
theorem flowFixedTimeInteriorStatement_of_thm13 (hT13 : Exist.Theorem13Statement.{u}) :
    GW2aStep.FlowFixedTimeInteriorStatement.{u} :=
  flowFixedTimeInteriorStatement_of_absorbedMerge fixedTimeAbsorbedMergeStatement hT13

end GW2aForce

end Theorem14

end InteractingSLE
