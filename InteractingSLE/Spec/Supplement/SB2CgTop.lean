/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CgZero

/-!
# `hTL` of Theorem 1.4's top from the remaining owners' inputs

Packet PROVE-SB2-CONDFIN (round 2). With the range identity (`Cg.sb2LowerRangeTWStatement`), the zero clause
(`Cg.sb2LowerZeroClauseWStatement`) and the data (`Cg.sb2LowerRelDriverStatementTWR_of_rest`) discharged,
**`sb2LowerTailLiftExStatement_of_rest`** gives `Lk.SB2LowerTailLiftExStatement` — the hypothesis `hTL` of
`Wire.theorem14Statement_assembled7` — from Theorems 1.2–1.3 and:

* `Nv.SB2LowerGeomRestV6Statement` (LIFTSET's remaining v6 input, D36 (2));
* `Mz.SB2LowerStageCanonStatement` (LIFTSET's joint induction, D29/D32);
* `Cf.SB2LowerRelPosWRootStatement` (the root of positive lifetime).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Theorem14.SB.Cg

open Exist

/-- **`hTL` from LIFTSET's v6 input, the canonical tail objects and the root** (Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_rest (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hR : Nv.SB2LowerGeomRestV6Statement.{u})
    (hcan : Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (hroot : Cf.SB2LowerRelPosWRootStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  Cf.sb2LowerTailLiftExStatement_of_inputs h12 h13 h12₀ h13₀
    (sb2LowerRelDriverStatementTWR_of_rest h12 h13 h12₀ h13₀ hR) (sb2LowerRangeTWStatement h12 h13 h12₀ h13₀)
    (sb2LowerZeroClauseWStatement h12 h13 h12₀ h13₀) hcan hroot

/-- **The conditional half over the corrected bundle from the canonical tail objects and the root**
(Theorems 1.2–1.3; the zero clause discharged). -/
theorem sb2LowerRelStageCondWStatement_of_canon_root (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hcan : Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (hroot : Cf.SB2LowerRelPosWRootStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Cf.SB2LowerRelStageCondWStatement.{u} :=
  Cf.sb2LowerRelStageCondWStatement h12 h13 h12₀ h13₀ (sb2LowerZeroClauseWStatement h12 h13 h12₀ h13₀) hcan hroot

end InteractingSLE.Theorem14.SB.Cg
