/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GR1FPositive
import InteractingSLE.Spec.Sec5.Aux61Asm2Build

/-! # Construct the five window fields of R1RestartInputs

An explicit positive or negative word and a buffered window determine the
fibre data. Replacing only the window fields of the restart choices leaves
the chart existence problem unchanged. All five window obligations then
follow from the actual construction, including the window's own clearance.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec5.Aux61GR1F
open Aux61Asm2 Aux61SlitW Aux61Fib Aux61FibData
universe u

/-- The deterministic geometry of a buffered window. -/
structure WindowGeometry where
  V : Set ℂ
  open_window : IsOpen V
  zero_window : (0 : ℂ) ∈ V
  O₀ : Set ℝ
  open_real : IsOpen O₀
  buffer : Set ℂ
  open_buffer : IsOpen buffer
  compact_buffer : IsCompact (closure buffer)
  real_buffer : ∀ z ∈ closure buffer, z.im = 0 → z.re ∈ O₀
  window_sub : V ⊆ buffer

/-- A reference word together with the actual forbidden interval. -/
structure ReferenceWord (κ : ℝ) where
  boundary : ℝ → ℝ
  jumps : Finset ℝ
  piecewise : IsPiecewiseConstantBoundaryData boundary jumps
  seed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ boundary jumps 0 0)
    (flowLineRhoR κ boundary jumps 0 0) 0 (flowLineXL boundary jumps 0) (flowLineXR boundary jumps 0)
  left : ℝ
  right : ℝ
  reference : Aux61Cov.RefWin κ boundary jumps (Ioo left right)

/-- Positive words satisfying the source height bound give reference data. -/
def positiveReference {κ a b v : ℝ} (hκ : 0 < κ) (hκ₄ : κ ≤ 4)
    (ha : 0 < a) (hab : a < b) (hv : sleLambda κ - Real.pi * chiC κ ≤ v) : ReferenceWord κ where
  boundary := positiveBoundary κ a b v
  jumps := {a, b, 0}
  piecewise := positiveBoundary_pc κ a b v
  seed := positiveBoundary_seed hκ ha hab
  left := a
  right := b
  reference := Or.inl (positiveBoundary_refPos hκ hκ₄ ha hv)

/-- Negative words use the landed strong-height reference construction. -/
def negativeReference {κ a b v : ℝ} (hκ : 0 < κ) (hκ₄ : κ < 4)
    (hab : a < b) (hb : b < 0) (hv : sleLambda κ + Real.pi * chiC κ < v) : ReferenceWord κ where
  boundary := Aux61GPrime.negativeBoundary κ a b v
  jumps := {a, b, 0}
  piecewise := Aux61GPrime.negativeBoundary_pc κ a b v
  seed := Aux61GPrime.negativeBoundary_seed hκ hab hb
  left := a
  right := b
  reference := Or.inr (Aux61GPrime.negativeBoundary_refNeg hκ hκ₄ hab hb hv subset_rfl)

/-- The fibre data of the constructed word/window, with zero reference
correction. The actual conditional mean correction is constructed later. -/
def referenceWindowData {κ : ℝ} (hκ : 0 < κ) (R : ReferenceWord κ) (G : WindowGeometry) : FibData :=
  fibDataOfWindow κ hκ R.boundary R.jumps R.piecewise R.seed G.V G.open_window G.zero_window
    (fun _ => 0) (InnerProductSpace.harmonicOnNhd_const 0) G.O₀ G.open_real
    (fun _ _ => tendsto_const_nhds) G.buffer G.open_buffer G.compact_buffer G.real_buffer G.window_sub

/-- Install the constructed word/window while retaining all chart and
record choices of the assembler's exact `R1Restart` structure. -/
def withWindowData {S : SourceSetting.{u}} (D : R1Restart S)
    (R : D.ι → ReferenceWord S.κ) (G : D.ι → WindowGeometry) : R1Restart S :=
  { D with data := fun i => referenceWindowData S.κ_pos (R i) (G i)
           left := fun i => (R i).left
           right := fun i => (R i).right }

theorem withWindowData_hasChart {S : SourceSetting.{u}} (D : R1Restart S)
    (R : D.ι → ReferenceWord S.κ) (G : D.ι → WindowGeometry) :
    (withWindowData D R G).HasChart ↔ D.HasChart := Iff.rfl

/-- The five window fields, with exactly the assembler's field types. -/
structure WindowFields {S : SourceSetting.{u}} (D : R1Restart S) : Prop where
  open_window : ∀ i, IsOpen (D.data i).V
  zero_window : ∀ i, (0 : ℂ) ∈ (D.data i).V
  clearance : ∀ i, (D.data i).ℓ = clr (D.data i).V
  kappa : ∀ i, (D.data i).κ = S.κ
  reference : ∀ i, Aux61Cov.RefWin (D.data i).κ (D.data i).bR (D.data i).JR (Ioo (D.left i) (D.right i))

/-- Every window field is proved for the explicitly constructed choices. -/
theorem withWindowData_fields {S : SourceSetting.{u}} (D : R1Restart S)
    (R : D.ι → ReferenceWord S.κ) (G : D.ι → WindowGeometry) :
    WindowFields (withWindowData D R G) where
  open_window i := (G i).open_window
  zero_window i := (G i).zero_window
  clearance _ := rfl
  kappa _ := rfl
  reference i := (R i).reference

end InteractingSLE.Sec5.Aux61GR1F
