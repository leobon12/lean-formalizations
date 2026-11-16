/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.LightConeAllQ.PieceTip
import InteractingSLE.Spec.Supplement.AbsMergeFlow
import InteractingSLE.Spec.Wire.T14Asm7

/-!
# The core of ruling R126 proved: interior switching tips at every deterministic schedule

Packet PROVE-T14-ALLQ. `gw2InteriorScheduleAllQ_holds` discharges the one-flow-line fixed-time statement of
`gw2InteriorScheduleAllQ_of_fix` by `GW2aForce.flowFixedTimeInteriorStatement_of_thm13` at the proved Theorem 1.3
(`Wire.T14Asm7.h13`), inline (rulings R48, R123).
-/

set_option autoImplicit false

universe u

namespace InteractingSLE.LightConeAllQ

/-- **GB9a's interior-switch condition at every deterministic countable dense schedule set** (ruling R126's core):
almost surely, before every launched instruction of a `Q`-schedule from the root `0` or a lower-arc root, every
switching tip is interior, for any given `Q`. -/
theorem gw2InteriorScheduleAllQ_holds : GW2InteriorScheduleAllQStatement.{u} :=
  gw2InteriorScheduleAllQ_of_fix (Theorem14.GW2aForce.flowFixedTimeInteriorStatement_of_thm13 Wire.T14Asm7.h13)

end InteractingSLE.LightConeAllQ
