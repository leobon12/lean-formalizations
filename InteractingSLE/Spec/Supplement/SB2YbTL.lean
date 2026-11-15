/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YbCond
import InteractingSLE.Spec.Supplement.SB2YaV5

/-!
# The hypothesis `hTL` of the current top from LIFTSET's v5 half and the conditional half

Packet PROVE-T14-SB2LIFT (round 31; decision D36). **`sb2LowerTailLiftExStatement_of_geomV5_condW`**: the hypothesis
`hTL : Lk.SB2LowerTailLiftExStatement` of `Wire.theorem14Statement_assembled7` from LIFTSET's
`Lk.SB2LowerGeomFactsV5Statement` and the conditional half over the corrected bundle
`Mq.SB2LowerRelStageCondWStatement` (CONDFIN, D36 (3)), and Theorems 1.2–1.3: the corrected data
`Lk.SB2LowerRelDriverStatementTW` is `Lk.sb2LowerRelDriverStatementTW_of_geomV5` (item 4 proved), and the range
identity is `Mq.sb2LowerTailLiftExStatement_of_relDriverTW_condW`. **`sb2LowerLaunchLiftStatement_of_geomV5_condW`**:
the same for `Lh.SB2LowerLaunchLiftStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Theorem14.SB.Mq

open Exist

/-- **`hTL` of `Wire.theorem14Statement_assembled7` from LIFTSET's v5 half and the conditional half over the
corrected bundle** (and Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_geomV5_condW (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hG : Lk.SB2LowerGeomFactsV5Statement.{u}) (hcond : SB2LowerRelStageCondWStatement.{u}) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  sb2LowerTailLiftExStatement_of_relDriverTW_condW h12 h13 h12₀ h13₀
    (Lk.sb2LowerRelDriverStatementTW_of_geomV5 h12 h13 h12₀ h13₀ hG) hcond

/-- **SB2(2)'s combined target (R104a) from LIFTSET's v5 half and the conditional half over the corrected bundle**
(and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_geomV5_condW (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hG : Lk.SB2LowerGeomFactsV5Statement.{u}) (hcond : SB2LowerRelStageCondWStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_relDriverTW_condW h12 h13 h12₀ h13₀
    (Lk.sb2LowerRelDriverStatementTW_of_geomV5 h12 h13 h12₀ h13₀ hG) hcond

end InteractingSLE.Theorem14.SB.Mq
