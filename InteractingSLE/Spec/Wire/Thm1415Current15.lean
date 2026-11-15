/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Current14
import InteractingSLE.Spec.Supplement.RLCRealCompletionWire
import InteractingSLE.Spec.Supplement.RLCG8DetRealMain
import InteractingSLE.Spec.Supplement.RLCHG2aWire
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj
import InteractingSLE.Spec.Sec7.Lemma76R
import InteractingSLE.Spec.Restart.FCThresholdDriverAEInputs
import InteractingSLE.Spec.Restart.RetPlumbProofAssembly
import InteractingSLE.Spec.Supplement.RLCG7aAssembly
import InteractingSLE.Spec.Wire.Thm1415CurrentRegularity
import InteractingSLE.Spec.Sec5.Prop49QExitMain
import InteractingSLE.Spec.Restart.FCK2Final
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYLimit

/-!
# Current conditional assembly of Theorem 1.5

All three interaction clauses and both companions are retained. Lemma 7.6
uses R55's boundary-stopped lifetime. G8's deterministic frame, transience,
the common-seed comparison and the chart-boundary input are discharged.
The expanded form displays the remaining conditional-law constructions.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Wire

/-- Lemma 7.5 from the current two Section 5 inputs. -/
theorem lemma75Statement_current (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) : Theorem15.Lemma75Statement.{u} :=
  lemma75Statement_of_open5 h411 h51
    (Sec7.Lemma71T.pocketClauseStatement (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411))

/-- The complete ordered reference used by G8 from the fixed-chart Lemma 7.1. -/
theorem prop74RefStatement_current (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) : Sec7.Prop74Order.Prop74RefStatement.{u} := by
  have href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  exact Sec7.Prop74Pocket.prop74RefStatement_of_twoMiddle href h55
    (Sec7.Prop74B.lemma71TwoMiddleStatement_of_fixedChart href h55
      (Sec7.Lemma71T.lemma71FixedChartStatement href) Sec7.Prop74B.pocketChartOrientationStatement)

/-- W5 from the current retained law, source-form G3, G7a and the G8 frame. -/
theorem w5Statement_current (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h77₀ : Supp10.Lemma77Statement.{0}) (hHist : RLC.RetainedCanonCondDetHistStatement.{u})
    (hG2a : RLC.G2aReferenceStatement.{0}) (hG3 : RLC.G3SourceStatement.{0})
    (hG7a : RLC.G7aChartStatement.{0}) (hG8 : RLC.G8FrameStatement.{0}) : Theorem15.W5Statement.{u} := by
  have href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have hD := RLC.retainedCanonCondDetUntouchedStatement_of_hist hHist
  have hRP := retainedKernelClockStatement_of_open5 h12₀ h13₀
    (RLC.retainedCanonCondDetStatement_of_untouched hD)
  have hCS := w5CommonSeedStatement_of_open5 h12 h13 h411 h51
    (Sec7.Lemma71T.pocketClauseStatement href) (Sec7.Lemma71T.lemma71FixedChartStatement href)
    (fun _ hκ _ => LocalExt.stoppedSeedExtendStatement hκ)
  exact RLC.w5Statement_of_g7a_param Theorem15.aux25Statement Supp7.w0aStatement
    (Supp9.w0bStatement_of_lemma75 (lemma75Statement_current h411 h51)) h77₀
    (Supp7.jointRetainedPairStatement_of_kernelClock hRP) hCS hG2a hG3 hG7a hG8
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hD

/-- Theorem 1.5 with every landed reduction on the R55/R60/R63 route plugged in.
The hypotheses are unresolved named statements, not additional source premises. -/
theorem theorem15Statement_current
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hDet : Sec7.Lemma76DetRStatement.{u}) (hDet₀ : Sec7.Lemma76DetRStatement.{0})
    (hHist : RLC.RetainedCanonCondDetHistStatement.{u}) (hHist₀ : RLC.RetainedCanonCondDetHistStatement.{0})
    (hFC : Restart.FirstContactCanonCondDetStatement.{u}) (hFC₀ : Restart.FirstContactCanonCondDetStatement.{0})
    (hG3 : RLC.G3SourceStatement.{0}) (hG7a : RLC.G7aChartStatement.{0}) : Theorem15Statement.{u} := by
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have h75 := lemma75Statement_current h411 h51
  have h75₀ := lemma75Statement_current h411₀ h51₀
  have h76 := Sec7.lemma76Statement_of_detR h12p₀ h13₀ h75 hDet
  have h76₀ := Sec7.lemma76Statement_of_detR h12p₀ h13₀ h75₀ hDet₀
  have h77 := lemma77Statement_of_open3 h76 h75
  have h77₀ := lemma77Statement_of_open3 h76₀ h75₀
  have hW := Restart.firstContactWordKernelStatement_of_param h75 h77 h12p₀ h13₀ hFC
  have hW₀ := Restart.firstContactWordKernelStatement_of_param h75₀ h77₀ h12p₀ h13₀ hFC₀
  have hR := WholeField.firstContactRestartLimStatement_of_lemmas Theorem15.aux25Statement h75 h77 hW
  have hG2a := RLC.g2aReferenceStatement_of_thm13 h13₀ h75₀ h77₀ hW₀
    (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411₀ h51₀)
  have hG8 := RLC.g8FrameStatement_of_proved_det_inputs h75₀
    (prop74RefStatement_current h411₀ h51₀) h12p₀ h13₀ hHist₀
  have hW5 := w5Statement_current h12 h13 h12₀ h13₀ h411 h51 h77₀ hHist hG2a hG3 hG7a hG8
  have hW5₀ := w5Statement_current h12₀ h13₀ h12₀ h13₀ h411₀ h51₀ h77₀ hHist₀ hG2a hG3 hG7a hG8
  have hRP := retainedKernelClockStatement_of_open5 h12₀ h13₀
    (RLC.retainedCanonCondDetStatement_of_untouched (RLC.retainedCanonCondDetUntouchedStatement_of_hist hHist))
  have hRP₀ := retainedKernelClockStatement_of_open5 h12₀ h13₀
    (RLC.retainedCanonCondDetStatement_of_untouched (RLC.retainedCanonCondDetUntouchedStatement_of_hist hHist₀))
  have hFH := Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP)
  have hFH₀ := Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP₀)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    exact stays_right_of_lt_of_remaining hW5 hFH (Supp9.w0bStatement_of_lemma75 h75)
      hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂
  · intro κ hκ hκ4 b jumps hb x₁ x₂ θ hx Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    exact merges_of_remaining h77 (Theorem15D5.firstContactRestartStatement_of_lim hR) h75 h75₀
      hκ hκ4 b jumps hb hx hh hη₁ hη₂
  · intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    exact crosses_of_lt_of_remaining h77 hR hW5₀ hFH₀ (Supp9.w0bStatement_of_lemma75 h75₀)
      hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂
  · intro κ hκ hκ4 b jumps hb x θ Ω _ P _ h hh
    exact exists_isFlowLine_of_wire6 h12 h13 hκ hκ4 hb hh
  · exact PiecewiseConstant.existsUnique_isBoundedHarmonicExtension

/-- Expanded leaves for Theorem 1.5. Theorem 1.3 supplies counterflow regularity
and nonreturn; G8 and the Gaussian hull-limit theorem are proved inputs.
Only the finite bypass, east-side comparison, stopped models and the retained,
first-contact and explicit-shift kernel constructions remain. -/
theorem theorem15Statement_current_expanded
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u}) (h47₀ : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (hfinite : Sec5.Prop51HTopo.FiniteWesternCrosscutBypassStatement)
    (hside : Sec5.Prop51I.FwdPostContactEastSideQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (hside₀ : Sec5.Prop51I.FwdPostContactEastSideQOn.{0}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → Restart.StoppedExtend.StoppedHullExtendStatement.{0} κ)
    (hModels : Restart.RetAux79.RetStoppedModelsStatement.{u})
    (hModels₀ : Restart.RetAux79.RetStoppedModelsStatement.{0})
    (hTouch : RLC.RetTouchMeanWordStatement.{u}) (hTouch₀ : RLC.RetTouchMeanWordStatement.{0})
    (hOrdDet : RLC.RetOrdDetStatement.{u}) (hOrdDet₀ : RLC.RetOrdDetStatement.{0})
    (hSafe : Restart.FCPlumb.FirstContactK2CapacitySafeLawsStatement.{u})
    (hSafe₀ : Restart.FCPlumb.FirstContactK2CapacitySafeLawsStatement.{0})
    (hTerminal : Restart.FCPlumb.FirstContactK2TerminalCollisionStatement.{u})
    (hTerminal₀ : Restart.FCPlumb.FirstContactK2TerminalCollisionStatement.{0})
    (hShift : Restart.FlowLocalityGen.ShiftKernelGenStatement.{0})
    (hThrough : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ) :
    Theorem15Statement.{u} := by
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_noReturn h47
    (counterflowNoReturnStatement_of_theorem13 h13)
  have h411₀ := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_noReturn h47₀
    (counterflowNoReturnStatement_of_theorem13 h13₀)
  have h51 := prop51QStatement_of_theorem13_current h13 hfinite hside
  have h51₀ := prop51QStatement_of_theorem13_current h13₀ hfinite hside₀
  have h75 := lemma75Statement_current h411 h51
  have h75₀ := lemma75Statement_current h411₀ h51₀
  have hDet := Restart.RetAux79.lemma76DetRStatement_of_stoppedModels hext h13₀ hModels
  have hDet₀ := Restart.RetAux79.lemma76DetRStatement_of_stoppedModels hext h13₀ hModels₀
  have h76 := Sec7.lemma76Statement_of_detR h12p₀ h13₀ h75 hDet
  have h76₀ := Sec7.lemma76Statement_of_detR h12p₀ h13₀ h75₀ hDet₀
  have hHist := RLC.retainedCanonCondDetHistStatement_of_touch_det h75 hTouch hOrdDet
  have hHist₀ := RLC.retainedCanonCondDetHistStatement_of_touch_det h75₀ hTouch₀ hOrdDet₀
  have hFC :=
    Restart.FCPlumb.firstContactCanonCondDetStatement_of_capacitySafeLaws_terminalCollision_thm12_thm13_lemma76
      h12 h13 h12₀ h13₀ h76 hSafe hTerminal
  have hFC₀ :=
    Restart.FCPlumb.firstContactCanonCondDetStatement_of_capacitySafeLaws_terminalCollision_thm12_thm13_lemma76
      h12₀ h13₀ h12₀ h13₀ h76₀ hSafe₀ hTerminal₀
  have hLimit : Restart.FlowStopIdentCMI.CMIXHullLocalityLimitStatement.{0} :=
    Restart.FlowStopIdentCMI.cmiXHullLocalityLimitStatement
  exact theorem15Statement_current h12 h13 h12₀ h13₀ h411 h51 h411₀ h51₀ hDet hDet₀ hHist hHist₀ hFC hFC₀
    (RLC.g3SourceStatement_of_kernel hShift hLimit hThrough h12p₀ h13₀)
    (RLC.g7aChartStatement_of_kernel hShift hLimit hThrough h12p₀ h13₀)

end InteractingSLE.Wire
