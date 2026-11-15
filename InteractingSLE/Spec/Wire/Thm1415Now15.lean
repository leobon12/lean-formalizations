/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Current15
import InteractingSLE.Spec.Wire.Thm1415NowSec5
import InteractingSLE.Spec.Supplement.RLCG7aHarmAssembly
import InteractingSLE.Spec.Restart.FCK2Term
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYProof

/-!
# Theorem 1.5 after the mean identity, converse, and terminal-access proofs

All five unchanged clauses are assembled. Part A supplies Lemma 4.7Q;
target-component (E1) supplies Proposition 5.1. G3's per-seed converse,
G7a's pocket mean identity, and first-contact physical terminal access are
proved. Retained and first-contact forward field kernels remain explicit.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Wire

/-- Conditional assembly with only the current Section 5, retained-law,
forward-kernel, and whole-field kernel inputs. This is not a sealed provider. -/
theorem theorem15Statement_now
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
    (hThrough : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ) :
    Theorem15Statement.{u} := by
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} := prop411QStatement_of_partA_clearance_now hA
  have h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0} := prop411QStatement_of_partA_clearance_now hA
  have h51 := prop51QStatement_of_partA_clearance_of_target_now hA htgt
  have h51₀ := prop51QStatement_of_partA_clearance_of_target_now hA htgt₀
  have h76 := Sec7.lemma76Statement_of_detR h12p₀ h13₀ (lemma75Statement_current h411 h51) hDet
  have h76₀ := Sec7.lemma76Statement_of_detR h12p₀ h13₀ (lemma75Statement_current h411₀ h51₀) hDet₀
  have hFC := Restart.FCPlumb.firstContactCanonCondDetStatement_of_forwardKernels_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76 hForward
  have hFC₀ := Restart.FCPlumb.firstContactCanonCondDetStatement_of_forwardKernels_thm12_thm13_lemma76
    h12₀ h13₀ h12₀ h13₀ h76₀ hForward₀
  exact theorem15Statement_current h12 h13 h12₀ h13₀ h411 h51 h411₀ h51₀
    hDet hDet₀ hHist hHist₀ hFC hFC₀
    (RLC.g3SourceStatement_of_through_param12_thm13 hThrough h12p₀ h13₀)
    (RLC.g7aChartStatement_of_harmonicIntegration hThrough h12p₀ h13₀)

/-- Expanded leaves: the deterministic clearance, mean identity, measurable-exit
converse, and physical terminal access are no longer hypotheses. The two
target-component inputs concern only excursions in the original right-target
component, as required by R71. -/
theorem theorem15Statement_now_expanded
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ))
    (htgt : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (htgt₀ : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{0}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → Restart.StoppedExtend.StoppedHullExtendStatement.{0} κ)
    (hModels : Restart.RetAux79.RetStoppedModelsStatement.{u})
    (hModels₀ : Restart.RetAux79.RetStoppedModelsStatement.{0})
    (hTouch : RLC.RetTouchMeanWordStatement.{u}) (hTouch₀ : RLC.RetTouchMeanWordStatement.{0})
    (hOrdDet : RLC.RetOrdDetStatement.{u}) (hOrdDet₀ : RLC.RetOrdDetStatement.{0})
    (hForward : Restart.FCPlumb.FirstContactK2ForwardKernelsStatement.{u})
    (hForward₀ : Restart.FCPlumb.FirstContactK2ForwardKernelsStatement.{0})
    (hThrough : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ) :
    Theorem15Statement.{u} := by
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_inverseBoundary hG5
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} := prop411QStatement_of_partA_clearance_now hA
  have h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0} := prop411QStatement_of_partA_clearance_now hA
  have h51 := prop51QStatement_of_partA_clearance_of_target_now hA htgt
  have h51₀ := prop51QStatement_of_partA_clearance_of_target_now hA htgt₀
  have hDet := Restart.RetAux79.lemma76DetRStatement_of_stoppedModels hext h13₀ hModels
  have hDet₀ := Restart.RetAux79.lemma76DetRStatement_of_stoppedModels hext h13₀ hModels₀
  have hHist := RLC.retainedCanonCondDetHistStatement_of_touch_det
    (lemma75Statement_current h411 h51) hTouch hOrdDet
  have hHist₀ := RLC.retainedCanonCondDetHistStatement_of_touch_det
    (lemma75Statement_current h411₀ h51₀) hTouch₀ hOrdDet₀
  exact theorem15Statement_now h12 h13 h12₀ h13₀ hA htgt htgt₀ hDet hDet₀ hHist hHist₀
    hForward hForward₀ hThrough

end InteractingSLE.Wire
