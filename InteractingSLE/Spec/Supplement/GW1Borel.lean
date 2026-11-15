/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1BorelGraph

/-!
# GW1 deterministic retargeting, including Borel measurability

Continuation of PROVE-GW1-DET. The Borel graph obligation left by the landed
`GW1Det` modules is now discharged. The original deterministic statement has
no additional hypothesis; its original probabilistic consumers retain only
their original probabilistic inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.GW1Det

/-- The full original deterministic retargeting statement: uniqueness when
retargeting exists, a Borel existence set, and a jointly measurable driver. -/
theorem detRetargetStatement : GW1Path.DetRetargetStatement :=
  detRetargetStatement_of_measurableSet_retargetGraph GW1Borel.measurableSet_retargetGraph

/-- The original GW1 pathwise retargeting reduction with both deterministic leaves proved. -/
theorem retargetPathStatement
    (hBR4a : BR4a.BR4aStatement.{u}) (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) :
    GW1Laws.RetargetPathStatement.{u} :=
  retargetPathStatement_of_measurableSet_retargetGraph hBR4a h12p hT13 hT13₀
    GW1Borel.measurableSet_retargetGraph

/-- The original finite retargeting law with no remaining deterministic input. -/
theorem finiteRetargetLawStatement
    (hBR4a : BR4a.BR4aStatement.{u}) (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) :
    GW1RestartPair.FiniteRetargetLawStatement.{u} :=
  finiteRetargetLawStatement_of_measurableSet_retargetGraph hBR4a h12p hT13 hT13₀
    GW1Borel.measurableSet_retargetGraph

end InteractingSLE.Theorem14.GW1Det
