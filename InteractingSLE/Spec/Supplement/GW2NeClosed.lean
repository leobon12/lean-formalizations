/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NeStmt
import InteractingSLE.Spec.Wire.T14Asm7

/-!
# `UncEndStatement` with Theorem 1.3 discharged

Packet PROVE-GW2-NEARIMG2, decision D56. `uncEndStatement` takes Theorem 1.3 as an argument; the landed proof
`Wire.T14Asm7.h13` discharges it. Kept in its own file so that `GW2NeStmt` stays light to import.

* **`uncEndStatement_closed`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Theorem14.GW2Ni

/-- **`UncEndStatement`, with no input.** -/
theorem uncEndStatement_closed : UncEndStatement.{u} := uncEndStatement Wire.T14Asm7.h13

end InteractingSLE.Theorem14.GW2Ni
