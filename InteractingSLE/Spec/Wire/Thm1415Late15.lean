/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Now15
import InteractingSLE.Spec.Wire.Thm1415LateRetain
import InteractingSLE.Spec.Supplement.RetChartClear
import InteractingSLE.Spec.Coupling.WFSLeafSurvEAssembly

/-!
# Theorem 1.5 after retained models, touching charts and the WFS reductions

The retained models and finite-lifetime endpoints are proved. Touching-side
functions and clearance are proved. WFS uses the continuous survival reader,
with the R79 extension and all later rule/clock approximation steps discharged.
The remaining model determination is exposed separately from model existence;
the obsolete arbitrary-stop extension statement is never a hypothesis here.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Wire

/-- Current conditional assembly with the WFS stochastic version input exposed. -/
theorem theorem15Statement_late
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (htgt : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (htgt₀ : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{0}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (hDet : Sec7.Lemma76DetRStatement.{u}) (hDet₀ : Sec7.Lemma76DetRStatement.{0})
    (hHist : RLC.RetainedCanonCondDetHistStatement.{u})
    (hHist₀ : RLC.RetainedCanonCondDetHistStatement.{0})
    (hForward : Restart.FCPlumb.FirstContactK2ForwardKernelsStatement.{u})
    (hForward₀ : Restart.FCPlumb.FirstContactK2ForwardKernelsStatement.{0})
    (hReader : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ContinuousSurvivalReaderStatement.{0} κ) :
    Theorem15Statement.{u} :=
  theorem15Statement_now h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀ hForward hForward₀
    (fun _ hκ hκ4 => WFS.throughKernelStatement_of_continuousSurvivalReader h12₀ h13₀ hκ
      (hReader _ hκ hκ4))

/-- Expanded leaves with models, touching sides, clearance, terminal access,
and WFS clock approximations supplied by landed theorems. -/
theorem theorem15Statement_late_expanded
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ))
    (htgt : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (htgt₀ : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{0}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (hMatch : RetStoppedTypeDeterminationStatement)
    (hZones : RLC.RetTouchZonesStatement)
    (hCollar : RLC.RetCollarMeanStatement.{u}) (hCollar₀ : RLC.RetCollarMeanStatement.{0})
    (hOrdDet : RLC.RetOrdDetStatement.{u}) (hOrdDet₀ : RLC.RetOrdDetStatement.{0})
    (hForward : Restart.FCPlumb.FirstContactK2ForwardKernelsStatement.{u})
    (hForward₀ : Restart.FCPlumb.FirstContactK2ForwardKernelsStatement.{0})
    (hReader : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ContinuousSurvivalReaderStatement.{0} κ) :
    Theorem15Statement.{u} := by
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_inverseBoundary hG5
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} := prop411QStatement_of_partA_clearance_now hA
  have h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0} := prop411QStatement_of_partA_clearance_now hA
  have h51 := prop51QStatement_of_partA_clearance_of_target_now hA htgt
  have h51₀ := prop51QStatement_of_partA_clearance_of_target_now hA htgt₀
  have h75 := lemma75Statement_current h411 h51
  have h75₀ := lemma75Statement_current h411₀ h51₀
  have hDet := lemma76DetRStatement_of_modelMatch_late hMatch h75
  have hDet₀ := lemma76DetRStatement_of_modelMatch_late hMatch h75₀
  have hTouch := RLC.retTouchMeanWordStatement_of_zones_collar h75 hZones hCollar
  have hTouch₀ := RLC.retTouchMeanWordStatement_of_zones_collar h75₀ hZones hCollar₀
  have hHist := RLC.retainedCanonCondDetHistStatement_of_touch_det h75 hTouch hOrdDet
  have hHist₀ := RLC.retainedCanonCondDetHistStatement_of_touch_det h75₀ hTouch₀ hOrdDet₀
  exact theorem15Statement_late h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀
    hForward hForward₀ hReader

end InteractingSLE.Wire
