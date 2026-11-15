/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1DetCode
import InteractingSLE.Spec.Supplement.GW1DetBoundaryWalk
import InteractingSLE.Spec.Supplement.GW1PathLeft

/-!
# GW1 deterministic retargeting: proved geometry and the remaining Borel graph

Packet PROVE-GW1-DET. `GW1Det.connectorPhysStatement` is unconditional.
`GW1Det.isRetargetOf_unique` is unconditional. The remaining obligation in
`DetRetargetStatement` is exactly `MeasurableSet GW1Det.retargetGraph`.
The two original pathwise reductions below use that named hypothesis explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

universe u

namespace InteractingSLE.Theorem14.GW1Det

/-- GW1's pathwise retargeting now needs only the Borel graph on the
deterministic side; the physical connector statement is proved. -/
theorem retargetPathStatement_of_measurableSet_retargetGraph
    (hBR4a : BR4a.BR4aStatement.{u}) (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hgraph : MeasurableSet retargetGraph) : GW1Laws.RetargetPathStatement.{u} :=
  GW1Path.retargetPathStatement_of_det hBR4a h12p hT13 hT13₀
    (detRetargetStatement_of_measurableSet_retargetGraph hgraph) connectorPhysStatement

/-- The finite retargeting law with the same single remaining deterministic
Borel graph obligation. -/
theorem finiteRetargetLawStatement_of_measurableSet_retargetGraph
    (hBR4a : BR4a.BR4aStatement.{u}) (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hgraph : MeasurableSet retargetGraph) : GW1RestartPair.FiniteRetargetLawStatement.{u} :=
  GW1Path.finiteRetargetLawStatement_of_det hBR4a h12p hT13 hT13₀
    (detRetargetStatement_of_measurableSet_retargetGraph hgraph) connectorPhysStatement

end InteractingSLE.Theorem14.GW1Det
