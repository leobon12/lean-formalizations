/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfDownRec

/-!
# The image word, its threshold, its flow-line type and the image field under the reflection `σ(z) = −z̄`

Packet PROVE-CFDOWN. The data of the chart form of Lemma 4.7's conditional law (`QSched.CfGivenChart44UpStatement`)
under the reflection: the image driver `W` becomes `−W`, the word `(xL; xR)`, `(ρL; ρR)` becomes `(−xR; −xL)`,
`(ρR; ρL)` (sides exchanged), and the field read in the image chart becomes the reflected field:

* `geomLW_neg`, `geomRW_neg`: the geometric force coordinates of the reflected word are the negated coordinates
  of the other side;
* **`thr_neg`**: the continuation threshold is unchanged;
* `FlowTypeAt`, `flowTypeAt_congr`, **`FlowTypeAt.reflect`**, **`isFlowType_reflWord`**: the reflected word is the
  angle-`0` flow-line word of the mirrored boundary word `Sec7.StripWall.reflWord c`;
* **`imgField_negRec`**: `imgField κ (negRec r) (reflField f) = reflField (imgField κ r f)`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfDown

open Exist.StagedLaw CfGiven
open LP (reflectC reflectC_reflectC)
open Sec7.FlowReflect (reflField reflTest reflData reflJumps)
open Sec7.PocketTraversal (geomLW geomRW)
open Restart (BoundaryWord)
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

variable {Ω : Type*} {nL nR : ℕ}

/-! ### The geometric word and its threshold -/

theorem geomLW_neg (W : ℝ≥0 → Ω → ℝ) (xR : Ω → Fin nR → ℝ) (i : Fin nR) (t : ℝ≥0) (ω : Ω) :
    geomLW (-W) (fun ω i => -xR ω i) i t ω = -geomRW W xR i t ω := by
  simp only [geomLW, geomRW, Pi.neg_apply, neg_neg]

theorem geomRW_neg (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (j : Fin nL) (t : ℝ≥0) (ω : Ω) :
    geomRW (-W) (fun ω j => -xL ω j) j t ω = -geomLW W xL j t ω := by
  simp only [geomLW, geomRW, neg_neg]
  rfl

/-- **The continuation threshold of the reflected word is unchanged.** -/
theorem thr_neg (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (ω : Ω) :
    Restart.FCDet.thr ρR ρL (-W) (fun ω i => -xR ω i) (fun ω j => -xL ω j) ω =
      Restart.FCDet.thr ρL ρR W xL xR ω := by
  unfold Restart.FCDet.thr MartChar.thresholdTime
  have hS : MartChar.thresholdSet ρR ρL (fun t => (-W) t ω)
      (fun i t => geomLW (-W) (fun ω i => -xR ω i) i t ω) (fun j t => geomRW (-W) (fun ω j => -xL ω j) j t ω) =
      MartChar.thresholdSet ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
        (fun j t => geomRW W xR j t ω) := by
    ext t
    simp only [MartChar.thresholdSet, mem_ofPred_eq, ForceWord.ThresholdCondition, geomLW_neg, geomRW_neg,
      Pi.neg_apply, neg_inj]
    exact or_comm
  rw [hS]

/-! ### The flow-line type -/

/-- The flow-line type of a word for arbitrary data `b`, jumps `J` and seed `x` (`FCDet.IsFlowType` is the case of a
boundary word and seed `0`). -/
def FlowTypeAt (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (x : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ (eL : flowLineNL b J x = nL) (eR : flowLineNR b J x = nR),
    (fun i => xL (Fin.cast eL i)) = flowLineXL b J x ∧
    (fun j => xR (Fin.cast eR j)) = flowLineXR b J x ∧
    (fun i => ρL (Fin.cast eL i)) = flowLineRhoL κ b J x θ ∧
    (fun j => ρR (Fin.cast eR j)) = flowLineRhoR κ b J x θ

theorem isFlowType_iff_flowTypeAt {κ θ : ℝ} {c : BoundaryWord} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} :
    Restart.FCDet.IsFlowType κ θ c xL xR ρL ρR ↔ FlowTypeAt κ θ c.fn c.jumps 0 xL xR ρL ρR := Iff.rfl

/-- The flow-line type written through the jump set `S` and the one-sided limits `lL`, `rL` of the data (the bodies of
`flowLineNL`, …, `flowLineRhoR`). -/
def FlowTypeData (κ θ : ℝ) (S : Finset ℝ) (lL rL : ℝ → ℝ) (x : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ (eL : (S.filter (· < x)).card + 1 = nL) (eR : (S.filter (x < ·)).card + 1 = nR),
    (fun i => xL (Fin.cast eL i)) = (Fin.cons 0 fun i => (S.filter (· < x)).orderEmbOfFin rfl (Fin.rev i) - x) ∧
    (fun j => xR (Fin.cast eR j)) = (Fin.cons 0 fun i => (S.filter (x < ·)).orderEmbOfFin rfl i - x) ∧
    (fun i => ρL (Fin.cast eL i)) = (Fin.cons (-(lL x + θ * chiC κ) / sleLambda κ - 1) fun i =>
      let y := (S.filter (· < x)).orderEmbOfFin rfl (Fin.rev i)
      (rL y - lL y) / sleLambda κ) ∧
    (fun j => ρR (Fin.cast eR j)) = (Fin.cons ((rL x + θ * chiC κ) / sleLambda κ - 1) fun i =>
      let y := (S.filter (x < ·)).orderEmbOfFin rfl i
      (rL y - lL y) / sleLambda κ)

theorem flowTypeAt_eq_data (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (x : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    FlowTypeAt κ θ b J x xL xR ρL ρR = FlowTypeData κ θ (jumpSet b J) (leftLim b) (rightLim b) x xL xR ρL ρR :=
  rfl

/-- The flow-line type sees the data only through its jump set and one-sided limits. -/
theorem flowTypeAt_congr {κ θ x : ℝ} {b b' : ℝ → ℝ} {J J' : Finset ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hJ : jumpSet b' J' = jumpSet b J) (hL : leftLim b' = leftLim b)
    (hR : rightLim b' = rightLim b) :
    FlowTypeAt κ θ b' J' x xL xR ρL ρR ↔ FlowTypeAt κ θ b J x xL xR ρL ρR := by
  rw [flowTypeAt_eq_data, flowTypeAt_eq_data, hJ, hL, hR]

/-- **The flow-line type under the reflection**: the reflected word is the angle-`(−θ)` flow-line word from `−x` of the
reflected data. -/
theorem FlowTypeAt.reflect {κ θ x : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (h : FlowTypeAt κ θ b J x xL xR ρL ρR) :
    FlowTypeAt κ (-θ) (reflData b) (reflJumps J) (-x) (fun i => -xR i) (fun j => -xL j) ρR ρL := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := h
  refine ⟨(Sec7.FlowReflect.flowLineNL_reflData hb x).trans eR, (Sec7.FlowReflect.flowLineNR_reflData hb x).trans eL,
    ?_, ?_, ?_, ?_⟩
  · funext j
    rw [Sec7.FlowReflect.flowLineXL_reflData_apply b J hb x j, ← hxR]
    rfl
  · funext j
    rw [Sec7.FlowReflect.flowLineXR_reflData_apply b J hb x j, ← hxL]
    rfl
  · funext j
    rw [Sec7.FlowReflect.flowLineRhoL_reflData_apply b J hb κ x θ j, ← hρR]
    rfl
  · funext j
    rw [Sec7.FlowReflect.flowLineRhoR_reflData_apply b J hb κ x θ j, ← hρL]
    rfl

/-- **The reflected word is the angle-`0` flow-line word of the mirrored boundary word.** -/
theorem isFlowType_reflWord {κ : ℝ} {c : BoundaryWord} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h : Restart.FCDet.IsFlowType κ 0 c xL xR ρL ρR) :
    Restart.FCDet.IsFlowType κ 0 (Sec7.StripWall.reflWord c) (fun i => -xR i) (fun j => -xL j) ρR ρL := by
  have h1 := FlowTypeAt.reflect c.isPiecewiseConstantBoundaryData (isFlowType_iff_flowTypeAt.1 h)
  rw [neg_zero] at h1
  have hfn : ∀ y ∉ reflJumps c.jumps, (Sec7.StripWall.reflWord c).fn y = reflData c.fn y := fun y hy =>
    Sec7.StripWall.fn_reflWord fun h' => hy (Sec7.FlowReflect.mem_reflJumps.2 h')
  rw [isFlowType_iff_flowTypeAt, Sec7.StripWall.jumps_reflWord,
    flowTypeAt_congr (Restart.jumpSet_congr hfn) (Restart.leftLim_congr hfn) (Restart.rightLim_congr hfn)]
  exact h1

/-! ### The image field -/

/-- **The field read in the reflected image chart is the reflected field read in the image chart.** -/
theorem imgField_negRec {κ : ℝ} (hκ : 0 < κ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    imgField κ (negRec r) (reflField f) = reflField (imgField κ r f) := by
  have hak : -(π * chiC κ) = π * chiC (16 / κ) := by rw [Sec4.chiC_sixteen_div hκ]; ring
  have h := Sec7.R7Outer.isChartTransport_infinitySourceChart_reflect hak (isChartTransport_imgField κ r f)
  have h2 := isChartTransport_imgField κ (negRec r) (reflField f)
  rw [recField_negRec] at h2
  exact h2.unique Chart.isConformal_infinitySourceChart h

theorem imgField_apply_eq {κ : ℝ} (hκ : 0 < κ) (r : RecData) (f : DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) :
    imgField κ r f φ = -imgField κ (negRec r) (reflField f) (reflTest φ) := by
  rw [imgField_negRec hκ, Sec7.FlowReflect.reflField_apply, Sec7.FlowReflect.reflTest_reflTest, neg_neg]

end InteractingSLE.Sec5.CfDown
