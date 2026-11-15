/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNodeClause
import InteractingSLE.Spec.Sec5.StagedS6Word

/-!
# Proposition 5.9's node laws: the arc killed word discharged

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-NODE kept PROVE-STAGED-S6's arc killed word as the named input
`StagedNode.ArcKilledWordStatement`; S6's `StagedS6.isKilledWord_arc` (landed) is exactly that statement.

* **`arcKilledWordStatement`**: `ArcKilledWordStatement` holds;
* **`nodePathOn_nodeObjects'`**: the path clause of every node law, with no arc input;
* **`nodeLawOn_nodeObjects'`**: `hNodeLaw` for `nodeObjects` from the comparison clause `NodeCompOn` and Part A's
  clearance form alone.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open Prop59Pieces StagedNode Wire.Night Restart Sec7.AdmCode

/-- **PROVE-STAGED-S6's arc killed word** (`StagedS6.isKilledWord_arc`) is the named input of PROVE-STAGED-NODE. -/
theorem arcKilledWordStatement : ArcKilledWordStatement :=
  fun hγ _ _ hxL hxR hxLa hxRm => StagedS6.isKilledWord_arc hγ hxL hxR hxLa hxRm

/-- **The path clause of every node law** for the stage objects with the recovered node noise, with the arc killed
word discharged. -/
theorem nodePathOn_nodeObjects' (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) : NodePathOn h44 (nodeObjects h44) :=
  nodePathOn_nodeObjects h44 arcKilledWordStatement hA

/-- **`hNodeLaw` for `nodeObjects` from the comparison clause alone** (and Part A's clearance form, as for the root
path). -/
theorem nodeLawOn_nodeObjects' (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hC : NodeCompOn h44 (nodeObjects h44)) : NodeLawOn h44 (nodeObjects h44) :=
  nodeLawOn_nodeObjects h44 arcKilledWordStatement hA hC

end InteractingSLE.Sec5.CrossCond.StagedNComp
