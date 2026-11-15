/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerLawWire
import InteractingSLE.Spec.Restart.FCKerDPath2

/-!
# Theorem 1.5's assemblies with the corrected first-contact kernels proved

Packet PROVE-T15-FCKER4. `FCKerLawWire`'s three assemblies of Theorem 1.5 (`theorem15Statement_nowC`, `_lateC`,
`_lateC_expanded`) take the corrected first-contact forward input `FirstContactK2ForwardKernelsCStatement` at both
universes. It is now proved from Theorems 1.2–1.3 and Lemma 7.6
(`Restart.FCPlumb.firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76'`), and Lemma 7.6 is produced inside
each assembly from its own inputs, so the input is dropped:

* **`theorem15Statement_nowD`**, **`theorem15Statement_lateD`**, **`theorem15Statement_lateD_expanded`**: the same
  statements without `hForward`, `hForward₀`.
-/

set_option autoImplicit false

noncomputable section

namespace InteractingSLE.Wire

universe u

/-- `theorem15Statement_nowC` with the corrected first-contact forward input discharged. -/
theorem theorem15Statement_nowD
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
    (hThrough : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ) :
    Theorem15Statement.{u} := by
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} := prop411QStatement_of_partA_clearance_now hA
  have h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0} := prop411QStatement_of_partA_clearance_now hA
  have h51 := prop51QStatement_of_partA_clearance_of_target_now hA htgt
  have h51₀ := prop51QStatement_of_partA_clearance_of_target_now hA htgt₀
  have h76 := Sec7.lemma76Statement_of_detR h12p₀ h13₀ (lemma75Statement_current h411 h51) hDet
  have h76₀ := Sec7.lemma76Statement_of_detR h12p₀ h13₀ (lemma75Statement_current h411₀ h51₀) hDet₀
  exact theorem15Statement_nowC h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀
    (Restart.FCPlumb.firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76' h12 h13 h76)
    (Restart.FCPlumb.firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76' h12₀ h13₀ h76₀) hThrough

/-- `theorem15Statement_lateC` with the corrected first-contact forward input discharged. -/
theorem theorem15Statement_lateD
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
    (hReader : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ContinuousSurvivalReaderStatement.{0} κ) :
    Theorem15Statement.{u} :=
  theorem15Statement_nowD h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀
    (fun _ hκ hκ4 => WFS.throughKernelStatement_of_continuousSurvivalReader h12₀ h13₀ hκ
      (hReader _ hκ hκ4))

/-- `theorem15Statement_lateC_expanded` with the corrected first-contact forward input discharged. -/
theorem theorem15Statement_lateD_expanded
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
  exact theorem15Statement_lateD h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀ hReader

end InteractingSLE.Wire
