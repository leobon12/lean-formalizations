/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRNextLines
import InteractingSLE.Spec.Supplement.BRLeafGB6

/-!
# GW4: deriving the word bounds without assuming a relative evolution

The field-determined canonical driver of a fixed boundary word is an ordinary
flow-line driver. It is used only to instantiate GW3's already available word
bounds, before the physical relative driver has been identified.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.Staged Sec7.StripSysField

/-- The canonical driver of a word is a flow-line driver of that word's field.
This does not identify any physical relative driver. -/
theorem isFlowLineDriver_cfDrv_word (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {k : ℝ} (hk : 0 < k) (c₀ : BoundaryWord)
    {Ω : Type u} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps) :
    IsFlowLineDriver k c₀.fn c₀.jumps 0 ν X
      (fun t ω => (BRLeaf.cfDrv h12p hk c₀ (X ω)).1 t)
      (fun ω => (BRLeaf.cfDrv h12p hk c₀ (X ω)).2) := by
  have hFw := Theorem15.isOrderedForceWord_flowLine c₀.fn c₀.jumps 0
  have hG := Exist.isGFFWithBoundaryData_flowField hk c₀.isPiecewiseConstantBoundaryData 0 0 hX
  have he : (fun ω => Exist.flowField 0 (0 * chiC k) (X ω)) = X := by
    funext ω
    rw [zero_mul]
    exact Sec5.GlueCond.flowField_zero_zero _
  rw [he] at hG
  obtain ⟨𝓕, VL, VR, B, hc⟩ := isOptionalHullCoupling_drv h12p h13 hk hFw hG
    ((BRLeaf.measurable_cfDrv h12p hk c₀).comp hX.1) (Eventually.of_forall fun _ => rfl)
  exact ⟨X, 𝓕, VL, VR, B, fun ω => isTranslateAddConst_zero_self _ _, hc⟩

/-- The inverted component field has precisely the infinity-source transport
used by the word-bound theorem. -/
theorem isChartTransport_invField {κ : ℝ} (hκ : 0 < κ) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) f (GW4Rel.invField κ f) := by
  rw [← GW4Rel.cfField_eq_invField hκ]
  exact GW4Traverse.isChartTransport_cfField κ f

end InteractingSLE.Theorem14.GW4Fix
