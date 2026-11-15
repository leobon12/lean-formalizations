/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJMain
import InteractingSLE.Spec.Wire.Thm12NightLaws

/-!
# Theorem 1.2's leaf `hRootLater` from the glued identifications

Packet PROVE-STAGED-REPJ. The leaf `hRootLater : Wire.Night.RootLaterOn h44 objects` of the expanded Theorem 1.2 (the
killed stage laws of PIECES' root candidates at every depth `j + 1`) splits into its path clause and its comparison
clause. The comparison clause is `compClauseK_rootCand_succ` (the transfer from the glued space, with PROVE-STAGED-S7's
killed representation); what remains of it are the two glued identifications, stated here for the whole setting:

* **`GluePastStatement`**: the `gZ`-preimages of `Gam`'s canonical past events of an admissible later list, inside its
  reached event, are almost surely events of the Galmarino filtration `candFilt` at time `0` inside the alive event;
* **`GlueObsStatement`**: almost surely on the alive event and `gZ⁻¹ gamR`, the canonical marks of `Gam`'s candidate are
  the `gC`-dilated restarted marks and its killed samples are those of the `gC`-dilated restarted word;
* `RootPathLaterOn`: the path clause at every depth `j + 1` (the later-stage analogue of `Wire.Night.RootPathOn`).

**`rootLaterOn_of_leaves`**: `RootLaterOn h44 objects` from these three and the clearance form of Part A (as for the
root stage, `Wire.Night.rootLaw_zero`). R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`; `h44` is R74's input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu hiding ratPt exists_ratPt_dist_lt
open Restart Exist.StagedLaw Exist.Staged Wire.Night
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System Prop59Sched
open StagedRepLater StagedKCand StagedKill StagedRep StagedCand StagedS4
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-- **The glued pasts of the later root stages** (named statement, `GluePast` everywhere). -/
def GluePastStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ),
    IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us →
    ∀ {q : ℚ} (hq : 0 < q) {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t),
      GluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq))

/-- **The glued observables of the later root stages** (named statement, `GlueObs` everywhere). -/
def GlueObsStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}),
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    ∀ {q : ℚ}, 0 < q → ∀ {j : ℕ} {t : Fin (j + 1) → ℝ≥0}, IsValid (j + 1) t →
      GlueObs x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t (q : ℝ).toNNReal

/-- **The path clause of the later root stages** (clause 1 of `Wire.Night.RootLaw … (j + 1) t`). -/
def RootPathLaterOn (h44 : Theorem12ParamCond44Statement.{0}) (objects : StageObjectsOn) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ (q : ℚ), 0 < q → ∀ (j : ℕ) (t : Fin (j + 1) → ℝ≥0),
      StagePath κ (P.prod d.measure)
        (canonQ (rootBase W ζ (Ωa := d.Ωa) q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t)
        (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (j + 1) t)
        (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
        (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
        (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ (j + 1))))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ (j + 1))))
        (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
            (canonXR x₀ hκ hb W ζ) q) (j + 1) t)
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q (j + 1) t).W
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q (j + 1) t).VL
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q (j + 1) t).VR
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q (j + 1) t).B
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q (j + 1) t).ζ

/-- **`hRootLater` from the path clause and the two glued identifications** (any stage objects; the comparison clause
is `compClauseK_rootCand_succ` with the clearance form of Part A for the good samples). -/
theorem rootLaterOn_of_leaves (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (objects : StageObjectsOn) (hPath : RootPathLaterOn h44 objects) (hpast : GluePastStatement h44)
    (hobs : GlueObsStatement h44) : RootLaterOn h44 objects := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω mΩ hSB P hP h W ζ γ hG hcf htr d q hq j t
  refine ⟨hPath hκ hκ4 hb P h W ζ γ hG hcf htr q hq j t, ?_⟩
  have hE := isStagedHistory_targetSched h44 hκ hκ4 hb hG
  have hR := stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG
  have hgood := fun r => rootGood_pieceZ_clearance x₀ h44 hκ hκ4 hb P d.measure h W ζ
    (Prop59Sched.targetSched (x₀ := x₀) h44 hκ hκ4 hb h) hA hG hcf hE hR r
  exact compClauseK_rootCand_succ x₀ h44 hκ hκ4 hb P d.measure h W ζ hG hcf hgood d.rootNoise hq t
    (fun us hus hv => hpast hκ hκ4 hb P h W ζ hG hcf us hus hq hv) (fun hv => hobs hκ hκ4 hb P h W ζ hG hcf hq hv)

end InteractingSLE.Sec5.CrossCond.StagedRepJ
