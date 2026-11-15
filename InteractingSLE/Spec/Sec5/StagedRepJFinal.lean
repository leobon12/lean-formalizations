/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJObs
import InteractingSLE.Spec.Sec5.StagedRepJPath

/-!
# Theorem 1.2's leaf `hRootLater` from the glued past and the marks identity

Packet PROVE-STAGED-REPJ. `GlueObsStatement` reduces to the marks identity of the later stages
(`glueObs_of_marks`, with `Gam`'s good set almost surely on the glued space, read off PIECES' space through the law of
the pair `map_pieceZ_eq`):

* **`GlueMarksStatement`** (named statement): almost surely on the alive event and `gZ⁻¹ gamR`, the tree marks of
  `Gam`'s candidate are the `rootLam`-dilated initial marks of the glued restarted word in tree order;
* `ae_gamGood_glue`, **`glueObsStatement_of_marks`**;
* **`rootLaterOn_s4Objects_of_marks`**: `RootLaterOn h44 (s4Objects h44)` from `GluePastStatement` and
  `GlueMarksStatement` (and the clearance form of Part A).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
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

/-- **The marks identity of the later root stages** (named statement, `GlueMarks` everywhere). -/
def GlueMarksStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}),
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    ∀ {q : ℚ}, 0 < q → ∀ {j : ℕ} {t : Fin (j + 1) → ℝ≥0}, IsValid (j + 1) t →
      GlueMarks x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t (q : ℝ).toNNReal

section Good

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

/-- **`Gam`'s good set holds almost surely on the glued space** (it holds on PIECES' space, clearance form of Part A,
and the pair has the same law on both spaces). -/
theorem ae_gamGood_glue (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∀ᵐ p ∂(gMu x₀ (κ := κ) P h W ζ hG.1), gZ x₀ (κ := κ) h p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := by
  have hE := isStagedHistory_targetSched h44 hκ hκ4 hb hG
  have hR := stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG
  have hg := rootGood_pieceZ_clearance x₀ h44 hκ hκ4 hb P (Measure.dirac (0 : ℝ)) h W ζ
    (Prop59Sched.targetSched (x₀ := x₀) h44 hκ hκ4 hb h) hA hG hcf hE hR 0
  have hZ := measurable_pieceZ (Ωa := ℝ) x₀ hG.1 hcf
  have hgamP : ∀ᵐ γ ∂((P.prod (Measure.dirac (0 : ℝ))).map (pieceZ (Ωa := ℝ) x₀ κ h W ζ)),
      γ ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb :=
    (ae_map_iff hZ.aemeasurable (measurableSet_gamGood h44 hκ hκ4 hb)).2 (hg.mono fun _ h' => h'.2)
  rw [map_pieceZ_eq x₀ P (Measure.dirac (0 : ℝ)) h W ζ hG.1 hcf] at hgamP
  exact (ae_map_iff (measurable_gZ x₀ h hG.1).aemeasurable (measurableSet_gamGood h44 hκ hκ4 hb)).1 hgamP

end Good

/-- **`GlueObsStatement` from the marks identity.** -/
theorem glueObsStatement_of_marks (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hm : GlueMarksStatement h44) : GlueObsStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ hG hcf q hq j t hv
  exact glueObs_of_marks x₀ h44 hκ hκ4 hb P h W ζ hv (ae_gamGood_glue x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf)
    (hm hκ hκ4 hb P h W ζ hG hcf hq hv)

/-- **Theorem 1.2's leaf `hRootLater`** for the concrete stage objects, from the glued past and the marks identity. -/
theorem rootLaterOn_s4Objects_of_marks (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (hpast : GluePastStatement h44) (hm : GlueMarksStatement h44) :
    RootLaterOn h44 (s4Objects h44) :=
  rootLaterOn_s4Objects_of_glue h44 hA hpast (glueObsStatement_of_marks h44 hA hm)

end InteractingSLE.Sec5.CrossCond.StagedRepJ
