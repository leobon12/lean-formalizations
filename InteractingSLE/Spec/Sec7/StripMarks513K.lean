/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripMarks513
import InteractingSLE.Spec.Sec7.StripMarksExpTree

/-!
# Proposition 5.13 for the strip system's counterflow from the concrete candidates' killed laws

Packet PROVE-STRIPMARKS. `StripMarks.h513_of_stripSystem` supplies Proposition 5.13 for the strip system's counterflow
from two abstract experiment families (`HistExp`, with their regularity, starts, events and candidate laws). Here the
experiments are the constructed ones (`StripMarks.prop513_path_of_candLaws`): only the killed laws of the fixed
concrete root and node candidates remain (with their noise and past data), besides the Figure 5.1 frame of the strip
word.

* **`h513_of_stripSystem_candLaws`**: `h513` of `StripMarksSource` (the centred chosen counterflow field) from the
  frame, `hword`, and the killed laws of the concrete candidates; the strip-to-parameter frame bridge is that of
  `Wire.late_prop513_comap_of_sched_frame` (`isStripGFF_parameterSource_of_word`, `isChartTransport_parameterSource`,
  `comap_eq_strip_parameter`, `comap_centredField_add`).

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.StripMarks

open WholeField PocketWordIn StripSysField
open Sec5 Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target Exist.StagedLaw Exist.Staged
  Sec7.AdmCode Restart Sec4 Theorem14.StagedReg Sec5.GlueCond Sec5.CrossCond.Word49 LawUnique
  Sec5.Prop59System Sec5.Prop59Stage Sec5.Prop59Pieces Sec5.Prop59Nodes Sec5.Prop59NodeTree Sec5.Prop59Tips
  Sec5.CrossCond.StagedK2 Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedCand Sec5.Prop59Sched Sec5.StripRevVisit
  Sec5.Prop513Asm Sec5.Prop513Bridge

/-- **Proposition 5.13 for the strip system's counterflow from the killed laws of the concrete candidates**: the
measurable version of the counterflow for the centred chosen counterflow field. The flow-line driver, its word, the
lifetime and the trace come from the strip system (`stripCounterflow_isFlowLineDriver`); the root and node
experiments are constructed (`prop513_path_of_candLaws`) in the parameter chart `fig51Source (16/k) x₀` of the chosen
counterflow field. -/
theorem h513_of_stripSystem_candLaws
    (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hFH : StagedPrefixFirstHitStatement.{0})
    {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem (16 / k) b J P h W ζ E) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (f : Frame) (hκ : 0 < 16 / k) (hκ4 : 16 / k < 4) (hb : IsFig51Bounds (16 / k) f.a f.b f.a' f.b')
    (hword : ∀ x ∉ counterflowJumps J ∪ Prop513Field.jumps (Real.exp (π * f.x₀)) (stripHJumps {0} {f.x₀}),
      counterflowData (16 / k) b x = stripCounterflowData (16 / k) 0 (Real.exp (π * f.x₀))
        (fig51Lower f.a f.b) (fig51Upper f.x₀ f.a' f.b') x)
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (noise₀ : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base₀ : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase₀ : ∀ q, base₀ q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw₀ : let hP := fig51Source (16 / k) f.x₀ (counterflowObjects hS.counterflow).field
      ∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFarK (16 / k) (P.prod Pa)
      (canonQ (base₀ q) (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ)
        (canonXR f.x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart f.x₀ hκ hb (canonXL f.x₀ hκ hb W ζ) (canonXR f.x₀ hκ hb W ζ) q) j t)
      (canonR (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ)
        (canonXR f.x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart f.x₀ hκ hb (canonXL f.x₀ hκ hb W ζ) (canonXR f.x₀ hκ hb W ζ) q) univ j t)
      (stageρL (16 / k) (rootρL (16 / k) (sourceWord (x₀ := f.x₀) hκ hb)) j)
      (stageρR (16 / k) (rootρR (16 / k) (sourceWord (x₀ := f.x₀) hκ hb)) j)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
      (canonY (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ)
        (canonXR f.x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) (rootStart f.x₀ hκ hb (canonXL f.x₀ hκ hb W ζ)
          (canonXR f.x₀ hκ hb W ζ) q) j t)
      (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ) (canonXR f.x₀ hκ hb W ζ)
        noise₀ (Ωa := Ωa) q j t).W
      (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ) (canonXR f.x₀ hκ hb W ζ)
        noise₀ (Ωa := Ωa) q j t).VL
      (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ) (canonXR f.x₀ hκ hb W ζ)
        noise₀ (Ωa := Ωa) q j t).VR
      (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ) (canonXR f.x₀ hκ hb W ζ)
        noise₀ (Ωa := Ωa) q j t).B
      (rootCand f.x₀ h44 hκ hκ4 hb P hP W ζ (canonLam W ζ) (canonXL f.x₀ hκ hb W ζ) (canonXR f.x₀ hκ hb W ζ)
        noise₀ (Ωa := Ωa) q j t).ζ)
    (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : let hP := fig51Source (16 / k) f.x₀ (counterflowObjects hS.counterflow).field
      ∀ (n : ℕ) (q : ℚ), 0 < q → ∀ j t, IsStageLawFarK (16 / k) (P.prod Pa)
      (canonQ (nodeBase f.x₀ h44 hκ hκ4 hb P hP W ζ noise base n q)
        (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q) ratGrid
        (nodeNL_pos f.x₀ hκ hb n) (nodeNR_pos f.x₀ hκ hb n) (nodeStart f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q) j t)
      (canonR (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q) ratGrid (nodeNL_pos f.x₀ hκ hb n)
        (nodeNR_pos f.x₀ hκ hb n) (nodeStart f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q)
        (nodeR0 f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q) j t)
      (stageρL (16 / k) (nodeρL (16 / k) (sourceWord (x₀ := f.x₀) hκ hb) (scheduleAt n)) j)
      (stageρR (16 / k) (nodeρR (16 / k) (sourceWord (x₀ := f.x₀) hκ hb) (scheduleAt n)) j)
      (farL (Nat.lt_of_lt_of_le (nodeNL_pos f.x₀ hκ hb n) (Nat.le_add_right _ j)))
      (farR (Nat.lt_of_lt_of_le (nodeNR_pos f.x₀ hκ hb n) (Nat.le_add_right _ j)))
      (canonY (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q)
        (nodeStart f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q) j t)
      (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q j t).W
      (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q j t).VL
      (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q j t).VR
      (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q j t).B
      (nodeCand (Ωa := Ωa) f.x₀ h44 hκ hκ4 hb P hP W ζ noise n q j t).ζ)
    (u : ℂ → ℝ) :
    let d := counterflowObjects hS.counterflow
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => centredField d.field d.mean ω + smoothDist upperHalfPlaneOpens u) inferInstance]
        fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t := by
  intro d
  have hfl := stripCounterflow_isFlowLineDriver hS
  have hbP := isPiecewiseConstant_counterflowData (16 / k) hS.boundaryData
  have hG := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
    (div_pos (by norm_num) hκ) hbP hfl
  have hGF := isStripGFF_parameterSource_of_word hκ hbP hG hword
  have hTF : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * f.x₀)))
      (-1) (-(π * chiC (16 / k))) (chiC (16 / (16 / k))) (fig51Source (16 / k) f.x₀ d.field ω) (d.field ω) :=
    fun ω => isChartTransport_parameterSource (Real.exp_pos _) _ _ (d.field ω)
  have hcf : IsStripCounterflowDriver (16 / k) 0 (Real.exp (π * f.x₀)) P
      (fig51Source (16 / k) f.x₀ d.field) W ζ := by
    refine ⟨counterflowData (16 / k) b, counterflowJumps J, d.field, hbP, ?_, hfl⟩
    simpa only [zero_add] using hTF
  have htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t : ℝ≥0 => η ω t) := by
    filter_upwards [hηtr, hS.lifetime] with ω hω hζ
    rw [hζ]
    exact hω
  rw [comap_centredField_add]
  obtain ⟨Γ', hm, he⟩ := prop513_path_of_candLaws h44 hA hFH hκ hκ4 hb
    (𝒢 := MeasurableSpace.comap (fig51Source (16 / k) f.x₀ d.field) inferInstance) (comap_measurable _)
    hGF hcf htr noise₀ base₀ hbase₀ hlaw₀ noise base hbase hlaw
  refine ⟨Γ', ?_, he⟩
  intro t
  rw [← comap_eq_strip_parameter (Real.exp_pos _) hTF]
  exact hm t

/-! ### Choosing the strip word from the Figure 5.1 frame -/

/-- `counterflowData κ` inverts `returnData (cfOffset κ) (cfCoeff κ)` off `0` (the other half of
`StripSysField.returnData_inverseData`). -/
theorem counterflowData_returnData (κ : ℝ) (g : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    counterflowData κ (returnData (cfOffset κ) (cfCoeff κ) g) x = g x := by
  have h := liftBoundary_add_liftBoundary_negInv hx
  simp only [counterflowData, inverseData, returnData, inv_neg, inv_inv, neg_neg]
  linear_combination (-cfCoeff κ) * h

/-- **The Figure 5.1 identity `hword` from the choice of the strip word**: if the strip word is the return data of the
Figure 5.1 counterflow word, the identity of `h513_of_stripSystem_candLaws` (and of `Wire.late_reference513`) holds
off any finite set containing `counterflowJumps J`. -/
theorem hword_of_eq_returnData {κ : ℝ} {b g : ℝ → ℝ} (J T : Finset ℝ)
    (hb : b = returnData (cfOffset κ) (cfCoeff κ) g) :
    ∀ x ∉ counterflowJumps J ∪ T, counterflowData κ b x = g x := by
  intro x hx
  have hx0 : x ≠ 0 := fun h0 => hx (Finset.mem_union_left _ (h0 ▸ Finset.mem_insert_self 0 _))
  rw [hb]
  exact counterflowData_returnData κ g hx0

end InteractingSLE.Sec7.StripMarks
