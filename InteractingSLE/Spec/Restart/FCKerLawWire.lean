/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Late15
import InteractingSLE.Spec.Restart.FCKerLawC

/-!
# Theorem 1.5's current assemblies with the corrected first-contact forward input

Packet PROVE-T15-FCKER2. `Restart.FCPlumb.FirstContactK2ForwardKernelsStatement` (an input of
`Wire.theorem15Statement_now`, `_late` and `_late_expanded`) is refuted by
`Restart.FCPlumb.FCKerLaw.measure_meetSet_eq_zero_of_forwardKernels`. The three assemblies below are the same
proofs with that input replaced by the corrected `Restart.FCPlumb.FirstContactK2ForwardKernelsCStatement` (through
`firstContactCanonCondDetStatement_of_forwardKernelsC_thm12_thm13_lemma76`). Every other hypothesis is unchanged.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Wire

/-- `theorem15Statement_now` with the corrected first-contact forward input. -/
theorem theorem15Statement_nowC
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
    (hForward : Restart.FCPlumb.FirstContactK2ForwardKernelsCStatement.{u})
    (hForward₀ : Restart.FCPlumb.FirstContactK2ForwardKernelsCStatement.{0})
    (hThrough : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ) :
    Theorem15Statement.{u} := by
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} := prop411QStatement_of_partA_clearance_now hA
  have h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0} := prop411QStatement_of_partA_clearance_now hA
  have h51 := prop51QStatement_of_partA_clearance_of_target_now hA htgt
  have h51₀ := prop51QStatement_of_partA_clearance_of_target_now hA htgt₀
  have h76 := Sec7.lemma76Statement_of_detR h12p₀ h13₀ (lemma75Statement_current h411 h51) hDet
  have h76₀ := Sec7.lemma76Statement_of_detR h12p₀ h13₀ (lemma75Statement_current h411₀ h51₀) hDet₀
  have hFC := Restart.FCPlumb.firstContactCanonCondDetStatement_of_forwardKernelsC_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76 hForward
  have hFC₀ := Restart.FCPlumb.firstContactCanonCondDetStatement_of_forwardKernelsC_thm12_thm13_lemma76
    h12₀ h13₀ h12₀ h13₀ h76₀ hForward₀
  exact theorem15Statement_current h12 h13 h12₀ h13₀ h411 h51 h411₀ h51₀
    hDet hDet₀ hHist hHist₀ hFC hFC₀
    (RLC.g3SourceStatement_of_through_param12_thm13 hThrough h12p₀ h13₀)
    (RLC.g7aChartStatement_of_harmonicIntegration hThrough h12p₀ h13₀)

/-- `theorem15Statement_late` with the corrected first-contact forward input. -/
theorem theorem15Statement_lateC
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
    (hForward : Restart.FCPlumb.FirstContactK2ForwardKernelsCStatement.{u})
    (hForward₀ : Restart.FCPlumb.FirstContactK2ForwardKernelsCStatement.{0})
    (hReader : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ContinuousSurvivalReaderStatement.{0} κ) :
    Theorem15Statement.{u} :=
  theorem15Statement_nowC h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀ hForward hForward₀
    (fun _ hκ hκ4 => WFS.throughKernelStatement_of_continuousSurvivalReader h12₀ h13₀ hκ
      (hReader _ hκ hκ4))

/-- `theorem15Statement_late_expanded` with the corrected first-contact forward input. -/
theorem theorem15Statement_lateC_expanded
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
    (hForward : Restart.FCPlumb.FirstContactK2ForwardKernelsCStatement.{u})
    (hForward₀ : Restart.FCPlumb.FirstContactK2ForwardKernelsCStatement.{0})
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
  exact theorem15Statement_lateC h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀
    hForward hForward₀ hReader

end InteractingSLE.Wire
