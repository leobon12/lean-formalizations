/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBW5Middle
import InteractingSLE.Spec.Wire.T15AsmLeaves
import InteractingSLE.Spec.Wire.Thm12BeaconInputs
import InteractingSLE.Spec.Sec5.ChartRawMembers

/-!
# W5 and the SB comparisons from the dyadic fibre cover

W5, SB1, and S6 follow from Theorems 1.2 and 1.3 and the dyadic fibre cover
at universes `u` and `0`. Part A and Proposition 4.11Q hold without inputs;
Beacon's Proposition 5.1 route uses the fibre cover without a retargeting
hypothesis. These results supply the ordered references in the intermediate
reduction below. The retained kernels, G3, G7a, and G8's deterministic geometry
are discharged by existing theorems. SB1 and S6 use the proved middle
exclusions and G15.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.SB.W5Assembly

/-- W5 with its conditional-law and local-comparison inputs discharged.
The ordered-reference hypotheses are discharged by `w5Statement_of_dyCover`. -/
theorem w5Statement_of_ordered_references
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h74 : Sec7.Prop74Order.Prop74RefStatement.{u})
    (h74₀ : Sec7.Prop74Order.Prop74RefStatement.{0})
    (h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{0}) : Theorem15.W5Statement.{u} := by
  have h75 := Restart.FCPlumb.lemma75Statement_of_thm12_thm13 h12 h13
  have h75₀ := Restart.FCPlumb.lemma75Statement_of_thm12_thm13 h12₀ h13₀
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hHist := Wire.T15Asm.retainedCanonCondDetHistStatement_of_lemma75 h75 h13₀
  have hHist₀ := Wire.T15Asm.retainedCanonCondDetHistStatement_of_lemma75 h75₀ h13₀
  have hD := RLC.retainedCanonCondDetUntouchedStatement_of_hist hHist
  have h76₀ := Sec7.lemma76Statement_of_detR h12p₀ h13₀ h75₀
    (Wire.T15Asm.lemma76DetRStatement_of_lemma75 h75₀ h13₀)
  have h77₀ := Restart.FCPlumb.lemma77Statement_of_thm12_thm13_lemma76 h12₀ h13₀ h76₀
  have hForward₀ :=
    Restart.FCPlumb.firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76'
      h12₀ h13₀ h76₀
  have hFC₀ :=
    Restart.FCPlumb.firstContactCanonCondDetStatement_of_forwardKernelsC_thm12_thm13_lemma76
      h12₀ h13₀ h12₀ h13₀ h76₀ hForward₀
  have hW₀ := Restart.firstContactWordKernelStatement_of_param h75₀ h77₀ h12p₀ h13₀ hFC₀
  have hG2a := RLC.g2aReferenceStatement_of_thm13 h13₀ h75₀ h77₀ hW₀ h55
  have hG8 := RLC.g8FrameStatement_of_proved_det_inputs h75₀ h74₀ h12p₀ h13₀ hHist₀
  have hThrough : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ :=
    fun _ hκ _ => WFS.throughKernelStatement h12₀ h13₀ hκ
  have hG3 := RLC.g3SourceStatement_of_through_param12_thm13 hThrough h12p₀ h13₀
  have hG7a := RLC.g7aChartStatement_of_harmonicIntegration hThrough h12p₀ h13₀
  have hRP := Wire.retainedKernelClockStatement_of_open5 h12₀ h13₀
    (RLC.retainedCanonCondDetStatement_of_untouched hD)
  have hCS := Supp9.w5CommonSeedStatement_of_germIdent
    (Sec7.Prop74Order.prop74OrderStatement_of_ref h75 h74)
    (Sec7.Aux97G.aux97GermIdentStatement_of_thm12_thm13 h12 h13)
  exact RLC.w5Statement_of_g7a_param Theorem15.aux25Statement Supp7.w0aStatement
    (Supp9.w0bStatement_of_lemma75 h75) h77₀
    (Supp7.jointRetainedPairStatement_of_kernelClock hRP) hCS hG2a hG3 hG7a hG8
    h12p₀ h13₀ hD

/-- W5 from Theorems 1.2–1.3 and the same fibre cover used by their assembly. -/
theorem w5Statement_of_dyCover
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem15.W5Statement.{u} := by
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} :=
    Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance
      (Wire.late_lemma47QHitStatement Sec5.ChartRaw.partAInputs) Sec5.ChartRaw.partAInputs
  have h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0} :=
    Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance
      (Wire.late_lemma47QHitStatement Sec5.ChartRaw.partAInputs) Sec5.ChartRaw.partAInputs
  have h51 := Wire.Beacon.prop51 Sec5.ChartRaw.partAInputs hDy
  have h51₀ := Wire.Beacon.prop51 Sec5.ChartRaw.partAInputs hDy0
  exact w5Statement_of_ordered_references h12 h13 h12₀ h13₀
    (Wire.prop74RefStatement_current h411 h51)
    (Wire.prop74RefStatement_current h411₀ h51₀)
    (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411₀ h51₀)

/-- SB1, including finite terminal endpoints, from the two fibre covers. -/
theorem sb1Statement_of_dyCover
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    SB1Statement.{u} :=
  W5Middle.sb1Statement_of_w5 (w5Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy0)

/-- S6, including finite terminal endpoints, from the two fibre covers. -/
theorem s6Statement_of_dyCover
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy0 : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    S6Statement.{u} :=
  W5Middle.s6Statement_of_w5 (w5Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy0)

end InteractingSLE.Theorem14.SB.W5Assembly
