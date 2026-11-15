/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrPast

/-!
# Theorem 1.2's leaf `hNodeLaw`: only the node marks identity remains

Packet PROVE-STAGED-NODETRANSFER. With the glued past proved (`nodeGluePast_of_partA`), PROVE-STAGED-NODECOMP's
`NodeTransferStatement h44` and the node laws `NodeLawOn h44 (nodeObjects h44)` follow from Part A's clearance form and
the node marks identity `NodeGlueMarksStatement` alone:

* **`nodeGluePastStatement_of_partA`**;
* **`nodeTransferStatement_of_marks`**, **`nodeCompOn_of_marks`**, **`nodeLawOn_nodeObjects_of_marks`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; `h44` is
R74's input.
-/

set_option autoImplicit false

noncomputable section

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open Wire.Night StagedNComp StagedNode Sec7.AdmCode Restart Prop513Target Prop59Sched

/-- **The glued pasts of the node candidates** (PROVED from Part A's clearance form). -/
theorem nodeGluePastStatement_of_partA (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) : NodeGluePastStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG hcf us _ n q hq j t hv
  exact nodeGluePast_of_partA x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf us n hq hv

/-- **PROVE-STAGED-NODECOMP's `NodeTransferStatement` from the node marks identities** (and Part A's clearance
form). -/
theorem nodeTransferStatement_of_marks (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hm : NodeGlueMarksStatement h44) : NodeTransferStatement h44 :=
  nodeTransferStatement_of_pastMarks h44 hA (nodeGluePastStatement_of_partA h44 hA) hm

/-- **The comparison clause of every node law** for `nodeObjects` from the node marks identities. -/
theorem nodeCompOn_of_marks (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hm : NodeGlueMarksStatement h44) : NodeCompOn h44 (nodeObjects h44) :=
  StagedNPath.nodeCompOn_of_transfer h44 (nodeTransferStatement_of_marks h44 hA hm)

/-- **`hNodeLaw` for `nodeObjects`** from the node marks identities and Part A's clearance form. -/
theorem nodeLawOn_nodeObjects_of_marks (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hm : NodeGlueMarksStatement h44) : NodeLawOn h44 (nodeObjects h44) :=
  StagedNPath.nodeLawOn_nodeObjects_of_transfer h44 hA (nodeTransferStatement_of_marks h44 hA hm)

end InteractingSLE.Sec5.CrossCond.StagedNTr
