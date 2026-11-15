/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightStage0

/-!
# Proposition 5.9 with its proved root comparison removed from the frontier

PROVE-WIRE-PARTA. Root stage zero needs only its path clause; KillArc and the
stopped-law transfer prove its comparison. Later root stages and node laws remain
named mathematical inputs (R78); no maximal trace is asserted past a far kill.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Night
open Sec4 Sec5 Sec5.Prop59Sched Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target
open Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart Sec7.Hsd
open Sec5.Prop59System Sec5.Prop59Stage Sec5.Prop59Pieces Sec5.Prop59Nodes Sec5.Prop59NodeTree
open Sec5.CrossCond.StagedK2 Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedCand
open Sec5.CrossCond.StagedRepLater LawUnique WangWu
open Sec5.GlueCond

/-- Noise and past data only; every law is a separate named predicate. -/
structure StageObjects (Ω : Type) [MeasurableSpace Ω] where
  Ωa : Type
  [mΩa : MeasurableSpace Ωa]
  [borel : StandardBorelSpace Ωa]
  measure : Measure Ωa
  [probability : IsProbabilityMeasure measure]
  rootNoise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ
  nodeNoise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ
  nodeBase : ℕ → ℚ → MeasurableSpace (Ω × Ωa)
attribute [instance] StageObjects.mΩa StageObjects.borel StageObjects.probability

/-- The path clause of `IsStageLawFarK`, with matching argument order. -/
def StagePath (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (_past : MeasurableSpace Ω) (R : Set Ω) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (_farL : Fin nL) (_farR : Fin nR) (y : Ω → Start nL nR)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧
    StrictAnti (y ω).2.1 ∧ StrictMono (y ω).2.2 ∧
    Sec2.IsSLEPathUpTo κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (ζ ω)

section Laws
variable (h44 : Theorem12ParamCond44Statement.{0})
  {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (d : StageObjects Ω)

def RootLaw (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0) : Prop :=
  IsStageLawFarK κ (P.prod d.measure)
        (canonQ (rootBase W ζ (Ωa := d.Ωa) q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) j t)
        (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ j t)
        (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) j)
        (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) j)
        (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
        (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
            (canonXR x₀ hκ hb W ζ) q) j t)
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q j t).W
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q j t).VL
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q j t).VR
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q j t).B
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q j t).ζ

def RootPath (q : ℚ) (t : Fin 0 → ℝ≥0) : Prop :=
  StagePath κ (P.prod d.measure)
        (canonQ (rootBase W ζ (Ωa := d.Ωa) q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) 0 t)
        (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ 0 t)
        (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) 0)
        (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) 0)
        (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ 0)))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ 0)))
        (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) d.rootNoise (Ωa := d.Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
            (canonXR x₀ hκ hb W ζ) q) 0 t)
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q 0 t).W
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q 0 t).VL
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q 0 t).VR
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q 0 t).B
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          d.rootNoise (Ωa := d.Ωa) q 0 t).ζ

def NodeLaw (n : ℕ) (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0) : Prop :=
  IsStageLawFarK κ (P.prod d.measure)
        (canonQ (nodeBase x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise d.nodeBase n q)
          (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid
          (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (canonR (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
          (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (canonY (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q)
          (nodeStart x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q) j t)
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).W
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VL
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).VR
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).B
        (nodeCand (Ωa := d.Ωa) x₀ h44 hκ hκ4 hb P h W ζ d.nodeNoise n q j t).ζ

/-- The root comparison is now proved, including KillArc; no law hypothesis for it remains. -/
theorem rootLaw_zero [StandardBorelSpace Ω] (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    {q : ℚ} (hq : 0 < q) (t : Fin 0 → ℝ≥0)
    (hpath : RootPath (x₀ := x₀) h44 hκ hκ4 hb P h W ζ d q t) : RootLaw (x₀ := x₀) h44 hκ hκ4 hb P h W ζ d q 0 t := by
  have hE := isStagedHistory_targetSched h44 hκ hκ4 hb hG
  have hR := stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG
  have hc := compClauseK_rootCand_clearance x₀ h44 hκ hκ4 hb P d.measure h W ζ
    (Prop59Sched.targetSched (x₀ := x₀) h44 hκ hκ4 hb h) hA hG.1 hG hcf hE hR d.rootNoise hq t
  refine ⟨hpath, ?_⟩
  simpa only [RootLaw, CompClauseK, consAlt, canonQ, canonR, canonY_zero, stageρL, stageρR, farL, farR,
    rootNL, rootNR, Fin.last, Nat.add_zero, Nat.add_sub_cancel, Nat.succ_sub_one] using hc
end Laws

/-- Choices for each genuine Figure 5.1 source case. -/
def StageObjectsOn :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    StageObjects Ω

def RootPathOn (h44 : Theorem12ParamCond44Statement.{0}) (objects : StageObjectsOn) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ (q : ℚ), 0 < q → ∀ t, RootPath (x₀ := x₀) h44 hκ hκ4 hb P h W ζ d q t

def RootLaterOn (h44 : Theorem12ParamCond44Statement.{0}) (objects : StageObjectsOn) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ (q : ℚ), 0 < q → ∀ j t, RootLaw (x₀ := x₀) h44 hκ hκ4 hb P h W ζ d q (j + 1) t

def NodeLawOn (h44 : Theorem12ParamCond44Statement.{0}) (objects : StageObjectsOn) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ j t, NodeLaw (x₀ := x₀) h44 hκ hκ4 hb P h W ζ d n q j t

def NodeBaseOn (h44 : Theorem12ParamCond44Statement.{0}) (objects : StageObjectsOn) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    ∀ hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀},
    ∀ hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ,
    ∀ htr : (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)),
    let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr;
    ∀ n q, d.nodeBase n q ≤ (inferInstance : MeasurableSpace (Ω × d.Ωa))

/-- The newest residual stage leaves imply the universal Figure 5.1 killed-law input. -/
theorem fig51CandLaws_of_parts (h44 : Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance) (objects : StageObjectsOn)
    (hPath : RootPathOn h44 objects) (hLater : RootLaterOn h44 objects)
    (hNode : NodeLawOn h44 objects) (hBase : NodeBaseOn h44 objects) : Fig51CandLawsStatement h44 := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω mΩ hSB P hP h W ζ γ hG hcf htr
  let d := objects hκ hκ4 hb P h W ζ γ hG hcf htr
  refine ⟨d.Ωa, d.mΩa, d.borel, d.measure, d.probability, d.rootNoise,
    (fun q => rootBase W ζ (Ωa := d.Ωa) q), d.nodeNoise, d.nodeBase, ?_, ?_,
    hBase hκ hκ4 hb P h W ζ γ hG hcf htr, hNode hκ hκ4 hb P h W ζ γ hG hcf htr⟩
  · intro q
    exact ((measurable_cfStop (q : ℝ).toNNReal).comp
      ((measurable_cfHistory_of_strip hcf).comp measurable_fst)).comap_le
  · intro q hq j t
    cases j with
    | zero =>
        exact rootLaw_zero h44 hκ hκ4 hb P h W ζ d hA hG hcf hq t
          (hPath hκ hκ4 hb P h W ζ γ hG hcf htr q hq t)
    | succ j => exact hLater hκ hκ4 hb P h W ζ γ hG hcf htr q hq j t

end InteractingSLE.Wire.Night
