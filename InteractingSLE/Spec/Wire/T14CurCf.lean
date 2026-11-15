/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T14CurSb2
import InteractingSLE.Spec.Supplement.SB2CfCond
import InteractingSLE.Spec.Wire.T14Asm7

/-!
# SB2(2)'s `hTL` through PROVE-SB2-CONDFIN's assembly: two of its five inputs discharged

Packet PROVE-T14-ASSEMBLE7 (round 2). PROVE-SB2-CONDFIN (c4dcb814f) assembles `hTL` as
`Cf.sb2LowerTailLiftExStatement_of_inputs` from five named inputs. Two of them are discharged here:

* **`T14Cur.sb2LowerRelDriverStatementTWR_of_restV6`**: CONDFIN's data with the root facts
  `Cf.SB2LowerRelDriverStatementTWR` from GEOM2's corrected v6 input `Nv.SB2LowerGeomRestV6Statement` (LIFTSET's),
  by the tail-free copy of GEOM2's v6 assembly (`Nv.sb2LowerRelDriverStatementTWR_of_restCur`, `T14CurSb2`);
* **`T14Cur.sb2LowerRangeTWStatement`**: CONDFIN's range identity `Cf.SB2LowerRangeTWStatement`, PROVED
  (`Mq.sb2LowerRangeTWStatementCur`, the range part of SB2LIFT's tail-free consumer);
* **`T14Cur.sb2LowerTailLiftExStatement_of_restV6_inputs`**: `hTL` from `Nv.SB2LowerGeomRestV6Statement` (LIFTSET),
  `Cf.SB2LowerZeroClauseWStatement` (the zero clause), `Mz.SB2LowerStageCanonStatement` (LIFTSET's joint induction) and
  `Cf.SB2LowerRelPosWRootStatement` (the root of positive lifetime), with Theorems 1.2–1.3.

Theorems 1.2–1.3 may be used (R48). No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Wire.T14Cur

open Theorem14

/-- **CONDFIN's data with the root facts from LIFTSET's v6 input** (Theorems 1.2–1.3). -/
theorem sb2LowerRelDriverStatementTWR_of_restV6 (hR : SB.Nv.SB2LowerGeomRestV6Statement.{u}) :
    SB.Cf.SB2LowerRelDriverStatementTWR.{u} :=
  SB.Nv.sb2LowerRelDriverStatementTWR_of_restCur T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hR

/-- **CONDFIN's range identity, PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerRangeTWStatement : SB.Cf.SB2LowerRangeTWStatement.{u} :=
  SB.Mq.sb2LowerRangeTWStatementCur T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀

/-- **`hTL` from LIFTSET's v6 input, the zero clause, the canonical tail objects and the root of positive lifetime**
(CONDFIN's `Cf.sb2LowerTailLiftExStatement_of_inputs` with the data and the range identity discharged). -/
theorem sb2LowerTailLiftExStatement_of_restV6_inputs (hR : SB.Nv.SB2LowerGeomRestV6Statement.{u})
    (hZ : SB.Cf.SB2LowerZeroClauseWStatement.{u})
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hroot : SB.Cf.SB2LowerRelPosWRootStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    SB.Lk.SB2LowerTailLiftExStatement.{u} :=
  SB.Cf.sb2LowerTailLiftExStatement_of_inputs T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀
    (sb2LowerRelDriverStatementTWR_of_restV6 hR) sb2LowerRangeTWStatement hZ hcan hroot

end InteractingSLE.Wire.T14Cur
