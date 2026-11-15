/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrMain

/-!
# Theorem 1.2's leaf `hNodeLaw` from the node glued identifications

Packet PROVE-STAGED-NODETRANSFER. PROVE-STAGED-NODECOMP's named input `NodeTransferStatement h44` (the transfer of
the node flags' stopped representation from the conditioned glued space to the node candidates `nodeCand` of
`nodeObjects`) follows from the clearance form of Part A and the two node glued identifications, stated here for the
whole setting:

* **`NodeGluePastStatement`**: the `gZ`-preimages of `Gam`'s canonical node past events of an admissible extension,
  inside its reached event, are almost surely events of the Galmarino filtration `candFiltF` at time `0` inside the
  alive event;
* **`NodeGlueObsStatement`**: almost surely on the alive event and `gZ⁻¹ gamNodeR`, the canonical marks of `Gam`'s
  node candidate are the restarted marks dilated by the node factor, and its killed samples are those of the dilated
  restarted word.

**`nodeTransferStatement_of_glue`**, then `nodeCompOn_of_glue` and **`nodeLawOn_nodeObjects_of_glue`** (with
PROVE-STAGED-NODEPATHS' `nodeFlagPathsStatement`). R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`; `h44` is R74's input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu hiding ratPt exists_ratPt_dist_lt
open Restart Exist.StagedLaw Exist.Staged Wire.Night
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open Prop59NodeTree StagedRepLater StagedKCand StagedKill StagedRep StagedRepJ StagedNComp StagedCand StagedNode
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-- **The glued pasts of the node candidates** (named statement, `NodeGluePast` everywhere). -/
def NodeGluePastStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ),
    IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us →
    ∀ (n : ℕ) {q : ℚ} (hq : 0 < q) {j : ℕ} {t : Fin j → ℝ≥0}
      (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)),
      NodeGluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq))

/-- **The glued observables of the node candidates** (named statement, `NodeGlueObs` everywhere). -/
def NodeGlueObsStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}),
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    ∀ (n : ℕ) {q : ℚ}, 0 < q → ∀ {j : ℕ} {t : Fin j → ℝ≥0},
      IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) →
      NodeGlueObs x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t (q : ℝ).toNNReal

/-- **PROVE-STAGED-NODECOMP's `NodeTransferStatement` from the node glued identifications** (and the clearance form of
Part A for the good samples). -/
theorem nodeTransferStatement_of_glue (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hpast : NodeGluePastStatement h44) (hobs : NodeGlueObsStatement h44) :
    NodeTransferStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d n q hq j t hrep
  exact compClauseK_nodeCand x₀ h44 hκ hκ4 hb P (Measure.dirac (0 : ℝ)) h W ζ
    (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) hA hG hcf hq t hrep
    (fun us hus hv => hpast hκ hκ4 hb P h W ζ hG hcf us hus n hq hv)
    (fun hv => hobs hκ hκ4 hb P h W ζ hG hcf n hq hv)

/-- **The comparison clause of every node law** for `nodeObjects`, from the node glued identifications. -/
theorem nodeCompOn_of_glue (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hpast : NodeGluePastStatement h44) (hobs : NodeGlueObsStatement h44) : NodeCompOn h44 (nodeObjects h44) :=
  StagedNPath.nodeCompOn_of_transfer h44 (nodeTransferStatement_of_glue h44 hA hpast hobs)

/-- **`hNodeLaw` for `nodeObjects`** from the node glued identifications and Part A's clearance form. -/
theorem nodeLawOn_nodeObjects_of_glue (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hpast : NodeGluePastStatement h44) (hobs : NodeGlueObsStatement h44) :
    NodeLawOn h44 (nodeObjects h44) :=
  StagedNPath.nodeLawOn_nodeObjects_of_transfer h44 hA (nodeTransferStatement_of_glue h44 hA hpast hobs)

end InteractingSLE.Sec5.CrossCond.StagedNTr
