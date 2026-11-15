/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkPastLaw
import InteractingSLE.Spec.Supplement.StagedDet

/-!
# Theorem 1.4: the retained past of a staged history is a Borel function of the field

Packet PROVE-T14-WALKLAW2. The named input `WalkLaw.PastDetRegStatement` of the union law of the two walks
(PROVE-T14-WALKLAW) is exactly the conclusion of PROVE-T14-SB7's `StagedDet.exists_pastMap_eq_comp_field` (Lemma GW1,
specification pp. 618–620: each piece is the flow line of the conditional field, hence by Theorem 1.2 a function of
it). Its inputs are the parametric Theorem 1.2 (`Theorem12ParamStatement`) and Theorem 1.3, which Theorem 1.4 may use
(rulings R43, R48: this file serves Theorem 1.4 only).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE

namespace Theorem14

namespace WalkLaw

/-- **The retained past of a staged history is almost surely a Borel function of the field** (`PastDetRegStatement`),
from the parametric Theorem 1.2 and Theorem 1.3 (PROVE-T14-SB7's induction over the stages). -/
theorem pastDetRegStatement_of_thm12_thm13 (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : PastDetRegStatement.{u} :=
  fun _ hκ hκ4 _ _ hb _ _ _ _ _ _ hh _ _ hE hR k =>
    StagedDet.exists_pastMap_eq_comp_field h12p h13 hκ hκ4 hb hh hE hR k

end WalkLaw

end Theorem14

end InteractingSLE
