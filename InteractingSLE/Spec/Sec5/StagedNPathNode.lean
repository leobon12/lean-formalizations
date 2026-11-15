/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNPathFlag

/-!
# Proposition 5.9's node flags: `NodeFlagPathsStatement` PROVED

Packet PROVE-STAGED-NODEPATHS. PROVE-STAGED-NODECOMP reduced the comparison clause of every node law
(`NodeCompOn h44 (nodeObjects h44)`, hence `hNodeLaw`) to two named inputs; this file proves the first one,
`NodeFlagPathsStatement h44` (PROVE-STAGED-S7's items 1 and 3 for the node flags), with no further input.

* `isStageWordN_of_cast`: a stage word transported along equalities of the index sizes;
* `flagExitWord_node`: for the node flags `nodeFlag s` at every node depth `nodeLen s + j` the restarted word
  `consAlt (bornL κ (nodeFlag s)) (nodeρL0 κ c θ₀) (nodeLen s + j)` is a stage word for its left span when `j` is even
  and (reflected) for its right span when `j` is odd: it is the node stage word `stageρL κ (nodeρL κ c s) j` up to
  the index cast `Fin (rootNL c + nodeLen s + j) ≃ Fin (rootNL c + (nodeLen s + j))` (`stageρL_nodeρL`), and the
  node word satisfies the initial-word conditions (`isStageInit_nodeρ`), so `hwL_of_isStageInit` /
  `hwR_of_isStageInit` apply;
* **`nodeFlagPathsStatement`**: `NodeFlagPathsStatement h44` from `flagPaths_of_exitWord`;
* **`nodeCompOn_of_transfer`**, **`nodeLawOn_nodeObjects_of_transfer`**: `NodeCompOn h44 (nodeObjects h44)` and
  `hNodeLaw` from the node transfer `NodeTransferStatement h44` alone (and Part A's clearance form for the latter).

Conditional helpers with distinct names; they replace no source theorem. R48: the only named inputs are `h44`
(`Theorem12ParamCond44Statement`, R74), Part A's clearance form and `NodeTransferStatement`; nothing uses Theorem
1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNPath

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater Prop59NodeTree
open Prop59Stage Prop59System StagedKCand StagedKill StagedRep StagedCand StagedAdapt StagedNode Wire.Night
open StagedNComp
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### The node flag words are stage words on one side -/

/-- **A stage word transported along equalities of the index sizes.** -/
theorem isStageWordN_of_cast {κ : ℝ} {nL nR nL' nR' : ℕ} (hL : nL = nL') (hR : nR = nR') {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {ρL' : Fin nL' → ℝ} {ρR' : Fin nR' → ℝ} (eL : ∀ i, ρL i = ρL' (Fin.cast hL i))
    (eR : ∀ j, ρR j = ρR' (Fin.cast hR j)) (h : IsStageWordN κ ρL ρR) : IsStageWordN κ ρL' ρR' := by
  subst hL hR
  have e1 : ρL = ρL' := funext eL
  have e2 : ρR = ρR' := funext eR
  subst e1 e2
  exact h

/-- **The restarted word of the node flags is a stage word on one side**: at node depth `nodeLen s + j`, for its
left span when `j` is even and (reflected) for its right span when `j` is odd. -/
theorem flagExitWord_node {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord}
    (hc : IsStageInit κ (rootρL κ c) (rootρR κ c)) (s : Schedule) (j : ℕ) :
    FlagExitWord κ c (nodeFlag s) (nodeLen s + j) := by
  have hI := isStageInit_nodeρ hκ hκ4 hc s
  rcases Nat.even_or_odd j with hev | hod
  · exact Or.inl (isStageWordN_of_cast (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) (stageρL_nodeρL κ c s j)
      (stageρR_nodeρR κ c s j) (hwL_of_isStageInit hκ hκ4 hI j hev))
  · exact Or.inr (isStageWordN_of_cast (Nat.add_assoc _ _ _) (Nat.add_assoc _ _ _) (stageρR_nodeρR κ c s j)
      (stageρL_nodeρL κ c s j) (hwR_of_isStageInit hκ hκ4 hI j (Nat.not_even_iff_odd.2 hod)))

/-! ### `NodeFlagPathsStatement` -/

/-- **PROVE-STAGED-S7's items 1 and 3 for the node candidates** (`NodeFlagPathsStatement`, PROVE-STAGED-NODECOMP's
first named input), PROVED: in every Figure 5.1 setting, for every node, positive rational counterflow time and
admissible extension of the node prefix, the flag candidate of the node flags starts strictly ordered, is killed at
its far marks with left limits and has a generating trace up to its lifetime, almost surely on its alive event. -/
theorem nodeFlagPathsStatement (h44 : Theorem12ParamCond44Statement.{0}) : NodeFlagPathsStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG hcf n q hq j t hv
  exact flagPaths_of_exitWord x₀ h44 hκ hκ4 hb P h W ζ _ hG hcf hv
    (Nat.lt_of_lt_of_le (nodeLen_pos (s := scheduleAt n)) (Nat.le_add_right _ _))
    ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq))
    (flagExitWord_node hκ hκ4 (isStageInit_sourceWord hκ hb) (scheduleAt n) j)

/-- **The comparison clause of every node law** for `nodeObjects`, from the node transfer alone. -/
theorem nodeCompOn_of_transfer (h44 : Theorem12ParamCond44Statement.{0}) (hT : NodeTransferStatement h44) :
    NodeCompOn h44 (nodeObjects h44) :=
  nodeCompOn_of_paths_transfer h44 (nodeFlagPathsStatement h44) hT

/-- **`hNodeLaw` for `nodeObjects`** from the node transfer and Part A's clearance form. -/
theorem nodeLawOn_nodeObjects_of_transfer (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hT : NodeTransferStatement h44) : NodeLawOn h44 (nodeObjects h44) :=
  nodeLawOn_nodeObjects_of_paths_transfer h44 hA (nodeFlagPathsStatement h44) hT

end InteractingSLE.Sec5.CrossCond.StagedNPath
