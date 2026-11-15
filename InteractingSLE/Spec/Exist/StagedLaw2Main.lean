/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawMain
import InteractingSLE.Spec.Exist.StagedLaw2Run
import InteractingSLE.Spec.Exist.StagedLaw2Word

/-!
# The staged conditional law from the single-stage law alone

Packet PROVE-STAGEDLAW2. With the two deterministic inputs proved (`runMeasStatement`, `wordMeasStatement`),
PROVE-STAGEDLAW's reduction gives `Staged.StagedCondLawStatement` and Theorem 1.4's companion from the single-stage law
`StopLawStatement` (and, for the companion, from the parametric Theorem 1.2 and Theorem 1.3).
-/

set_option autoImplicit false

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open Staged

/-- **The staged conditional law from the single-stage law.** -/
theorem stagedCondLawStatement_of_stopLaw (hA : StopLawStatement.{u}) : StagedCondLawStatement.{u} :=
  stagedCondLawStatement_of_inputs hA runMeasStatement wordMeasStatement

/-- **Theorem 1.4's companion construction from three inputs**: the parametric Theorem 1.2, Theorem 1.3 and the
single-stage law. -/
theorem stagedHistoryConstructionStatement_of_stopLaw' (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hA : StopLawStatement.{u}) : Theorem14.StagedHistoryConstructionStatement.{u} :=
  stagedHistoryConstructionStatement_of_stopLaw h12p h13 hA runMeasStatement wordMeasStatement

theorem regularStagedHistoryConstructionStatement_of_stopLaw' (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hA : StopLawStatement.{u}) : RegularStagedHistoryConstructionStatement.{u} :=
  regularStagedHistoryConstructionStatement_of_stopLaw h12p h13 hA runMeasStatement wordMeasStatement

end StagedLaw

end Exist

end InteractingSLE
