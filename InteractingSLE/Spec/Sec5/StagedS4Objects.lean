/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightLaws
import InteractingSLE.Spec.Sec5.StagedRepLaterClause
import InteractingSLE.Spec.Sec7.StripMarksExpGood

/-!
# Concrete stage objects for Proposition 5.9's killed laws; the root path leaf and the node-base leaf

Packet PROVE-STAGED-S4. The expanded Theorem 1.2 wiring (PROVE-WIRE-PARTA, `Wire.Night`) takes a choice of stage
objects `stageObjects : Night.StageObjectsOn` (an auxiliary noise space and the noise parameters of the candidates)
and four leaves about it: `RootPathOn`, `RootLaterOn`, `NodeLawOn`, `NodeBaseOn`. Here:

* **`s4Objects h44`**: the noise space `(ℝ, δ₀)`, the root noise PROVE-STAGED-REP2's recovered noise `rootNoise`
  (every killed word solves Definition 2.1's equations with it), node noise `0` and node bases `⊥`;
* **`rootPathOn_s4Objects`**: `RootPathOn h44 (s4Objects h44)` from the clearance form of Part A (the path clause of
  every stage-`0` root candidate: REP2's `clause1_rootCand_of_good` on the almost sure good events);
* **`nodeBaseOn_s4Objects`**: `NodeBaseOn h44 (s4Objects h44)`.

`RootLaterOn` (stages `j ≥ 1`, PROVE-STAGED-S3/S4's S3 route) and `NodeLawOn` remain open; when the node experiments
are built, their noise must be the node candidates' recovered noise (replace `nodeNoise` here; the two leaves proved
here do not read it). R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any
`*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Prop59System Prop59Stage Prop59Pieces Prop59Nodes Prop59Sched StagedKCand StagedKill StagedRep StagedRepLater
open Wire.Night LawUnique WangWu GlueCond Word49

/-- **Concrete stage objects**: noise space `(ℝ, δ₀)`, the recovered root noise of PROVE-STAGED-REP2, node noise `0`
and node bases `⊥`. -/
def s4Objects (h44 : Theorem12ParamCond44Statement.{0}) : StageObjectsOn :=
  fun {_ x₀ _ _ _ _} hκ hκ4 hb {_} _ _ P _ h W ζ _ _ _ _ =>
    { Ωa := ℝ
      measure := Measure.dirac 0
      rootNoise := rootNoise x₀ h44 hκ hκ4 hb P h W ζ
      nodeNoise := fun _ _ _ _ _ _ => 0
      nodeBase := fun _ _ => ⊥ }

/-- **The node-base leaf** for the concrete stage objects. -/
theorem nodeBaseOn_s4Objects (h44 : Theorem12ParamCond44Statement.{0}) : NodeBaseOn h44 (s4Objects h44) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d n q
  exact (bot_le : (⊥ : MeasurableSpace (Ω × ℝ)) ≤ _)

/-- **The root path leaf** for the concrete stage objects, from the clearance form of Part A: the path clause of
every stage-`0` root candidate (ordered strict junction start, Definition 2.1's integrated path with the recovered
noise up to the killed lifetime). -/
theorem rootPathOn_s4Objects (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance) :
    RootPathOn h44 (s4Objects h44) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d q hq t
  have hr : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  have h1 := rootGood_pieceZ_clearance x₀ h44 hκ hκ4 hb P (Measure.dirac (0 : ℝ)) h W ζ
    (Prop59Sched.targetSched h44 (x₀ := x₀) hκ hκ4 hb h) hA hG hcf (isStagedHistory_targetSched h44 hκ hκ4 hb hG)
    (stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG) (q : ℝ).toNNReal
  have h2 := Sec7.StripMarks.ae_cfHistory_mem_goodSet49_of_clearance hκ hκ4 hb hA hG hcf hr
  have h2' : ∀ᵐ ω' ∂(P.prod (Measure.dirac (0 : ℝ))), Cond44Ref.cfHistory W ζ ω'.1 ∈ goodSet49 (q : ℝ).toNNReal :=
    Measure.quasiMeasurePreserving_fst.ae h2
  show ∀ᵐ ω' ∂(P.prod (Measure.dirac (0 : ℝ))), _
  filter_upwards [h1, h2'] with ω' hω1 hω2 _
  exact clause1_rootCand_of_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 hcf t hω1.1 hω2

end InteractingSLE.Sec5.CrossCond.StagedS4
