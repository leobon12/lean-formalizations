/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCRealCompletionDatum
import InteractingSLE.Spec.Supplement.RLCG3SourceWire

/-!
# Theorem W5 and Theorem 1.5's wire6 clauses without the chart-level real-contact input

Packet PROVE-G3RESTART. The `wire6` route (`Spec/Wire/Thm15Inputs6.lean`, and its source-form-G3 copy
`Spec/Supplement/RLCG3SourceWire.lean`) takes the real-contact case of W5 as the named input `hChart :
RLC.RetainedChartRealCompletionStatement`. Here it is discharged:

* the interior case of W5 uses Lemma G3 in the source's form (`RLC.G3SourceStatement`, ruling R60), as in PROVE-G3SRC;
* the real-contact case uses `RLC.retainedChartRealCompletionAtStatement_of_g7a_param` (`RLCRealCompletionDatum.lean`):
  Corollary G7a (`RLC.G7aChartStatement`), the G8 frame (`RLC.G8FrameStatement`), G2a (derived from transience as in
  the `wire6` route) and the strengthened two-tip input `RLC.RetainedCanonCondDetUntouchedStatement` (which implies the
  `wire6` route's `Restart.RetainedCanonCondDetStatement`); W5 consumes the real case only at the common contact
  (`RLC.retainedLocalCompletionRealLocStatement_of_chartAt`), so the property at the contact suffices.

* **`RLC.w5Statement_of_g7a_param`**: Theorem W5 from the remaining W5 inputs, G2a, the source-form G3, G7a, G8,
  Theorems 1.2 (param) / 1.3 and the strengthened two-tip input;
* **`Wire.w5Statement_of_wire6_g7a`**, **`Wire.stays_right_of_lt_of_wire6_g7a`** (Theorem 1.5 (i)),
  **`Wire.crosses_of_lt_of_wire6_g7a`** (Theorem 1.5 (iii)): copies of the `…_wire6_src` results with `hChart`
  replaced by `hG7a`, `hG8` and the strengthened two-tip input. Clause (ii) (`Wire.merges_of_wire6`) and the companion
  never used W5's real case.

R43/R48: for Theorem 1.5 only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace RLC

/-- **Theorem W5** (`Theorem15.W5Statement`) from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the
common-seed comparison, G2a, Lemma G3 in the source's form (interior case), Corollary G7a and the G8 frame (real
case), Theorems 1.2 (param) / 1.3 and the strengthened two-tip input. -/
theorem w5Statement_of_g7a_param (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0})
    (hJ : Supp9D.JointRetainedPairStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u})
    (hG2a : G2aReferenceStatement.{0}) (hG3 : G3SourceStatement.{0}) (hG7a : G7aChartStatement.{0})
    (hG8 : G8FrameStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetUntouchedStatement.{u}) :
    Theorem15.W5Statement.{u} :=
  w5Statement_of_realLoc_param_src h25 hW0a hW0b h77 hJ hCS (g2ReferenceStatement_of_g2a hG2a) hG3 h12p h13
    (retainedCanonCondDetStatement_of_untouched hD)
    (retainedLocalCompletionRealLocStatement_of_chartAt
      (retainedChartRealCompletionAtStatement_of_g7a_param hG2a hG7a hG8 h12p h13 hD))

end RLC

namespace Wire

/-- Theorem W5 from the `wire6` inputs with the source-form G3 (interior case) and G7a with the G8 frame (real case),
in place of the chart-level real-contact input `RLC.RetainedChartRealCompletionStatement`. -/
theorem w5Statement_of_wire6_g7a (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hCB₀ : Sec7.Lemma76ChartBoundaryStatement.{0}) (hDet₀ : Sec7.Lemma76DetStatement.{0})
    (hRCDU : RLC.RetainedCanonCondDetUntouchedStatement.{u})
    (hFCD₀ : Restart.FirstContactCanonCondDetStatement.{0})
    (hTrans : RLC.G2aTransienceStatement.{0}) (hG3 : RLC.G3SourceStatement.{0})
    (hG7a : RLC.G7aChartStatement.{0}) (hG8 : RLC.G8FrameStatement.{0}) : Theorem15.W5Statement.{u} := by
  let href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  let href₀ := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411₀
  let hcl := Sec7.Lemma71T.pocketClauseStatement href
  let hcl₀ := Sec7.Lemma71T.pocketClauseStatement href₀
  let hfc := Sec7.Lemma71T.lemma71FixedChartStatement href
  let hD76₀ := lemma76CondDetHeightsStatement_of_wire6 h411₀ h51₀ hCB₀ hDet₀
  let h77₀ := lemma77Statement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hD76₀
  let hL75 := lemma75Statement_of_open5 h411 h51 hcl
  let hRCD := RLC.retainedCanonCondDetStatement_of_untouched hRCDU
  let hRP := retainedKernelClockStatement_of_open5 h12₀ h13₀ hRCD
  let hJ := Supp7.jointRetainedPairStatement_of_kernelClock hRP
  let hParts := RLC.g2aPartsStatement_of_transience hTrans
  let hG2a := RLC.g2aReferenceStatement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hD76₀ hFCD₀ h411₀ h51₀ hParts
  let hCS := w5CommonSeedStatement_of_open5 h12 h13 h411 h51 hcl hfc
    (fun _ hκ _ => LocalExt.stoppedSeedExtendStatement hκ)
  exact RLC.w5Statement_of_g7a_param Theorem15.aux25Statement Supp7.w0aStatement
    (Supp9.w0bStatement_of_lemma75 hL75) h77₀ hJ hCS hG2a hG3 hG7a hG8
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hRCDU

/-- Theorem 1.5 (i) on the `wire6` route with the source-form G3 and G7a with the G8 frame in place of the chart-level
real-contact input. -/
theorem stays_right_of_lt_of_wire6_g7a
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hRCDU : RLC.RetainedCanonCondDetUntouchedStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hCB₀ : Sec7.Lemma76ChartBoundaryStatement.{0}) (hDet₀ : Sec7.Lemma76DetStatement.{0})
    (hFCD₀ : Restart.FirstContactCanonCondDetStatement.{0})
    (hTrans : RLC.G2aTransienceStatement.{0}) (hG3 : RLC.G3SourceStatement.{0})
    (hG7a : RLC.G7aChartStatement.{0}) (hG8 : RLC.G8FrameStatement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁ := by assumption) (hθ : θ₁ < θ₂ := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ := by assumption) :
    (∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        ¬ IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) := by
  let href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  let hcl := Sec7.Lemma71T.pocketClauseStatement href
  let hL75 := lemma75Statement_of_open5 h411 h51 hcl
  let hW5 := w5Statement_of_wire6_g7a h12 h13 h12₀ h13₀ h411 h51
    h411₀ h51₀ hCB₀ hDet₀ hRCDU hFCD₀ hTrans hG3 hG7a hG8
  let hRP := retainedKernelClockStatement_of_open5 h12₀ h13₀ (RLC.retainedCanonCondDetStatement_of_untouched hRCDU)
  exact stays_right_of_lt_of_remaining hW5
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP))
    (Supp9.w0bStatement_of_lemma75 hL75) hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- Theorem 1.5 (iii) on the `wire6` route at universe `0` with the source-form G3 and G7a with the G8 frame in place
of the chart-level real-contact input. -/
theorem crosses_of_lt_of_wire6_g7a
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hCB : Sec7.Lemma76ChartBoundaryStatement.{u}) (hDet : Sec7.Lemma76DetStatement.{u})
    (hFCD : Restart.FirstContactCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hCB₀ : Sec7.Lemma76ChartBoundaryStatement.{0}) (hDet₀ : Sec7.Lemma76DetStatement.{0})
    (hRCDU₀ : RLC.RetainedCanonCondDetUntouchedStatement.{0})
    (hFCD₀ : Restart.FirstContactCanonCondDetStatement.{0})
    (hTrans : RLC.G2aTransienceStatement.{0}) (hG3 : RLC.G3SourceStatement.{0})
    (hG7a : RLC.G7aChartStatement.{0}) (hG8 : RLC.G8FrameStatement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ₁ θ₂ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ := by assumption)
    (hx : x₂ < x₁ := by assumption) (hθ : θ₂ < θ₁ := by assumption)
    (hθπ : θ₁ < θ₂ + Real.pi := by assumption) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) := by
  let href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  let href₀ := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411₀
  let hcl := Sec7.Lemma71T.pocketClauseStatement href
  let hcl₀ := Sec7.Lemma71T.pocketClauseStatement href₀
  let hD76 := lemma76CondDetHeightsStatement_of_wire6 h411 h51 hCB hDet
  let h77 := lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76
  let hR := firstContactRestartLimStatement_of_open5 h12₀ h13₀ h411 h51 hcl hD76 hFCD
  let hRP₀ := retainedKernelClockStatement_of_open5 h12₀ h13₀
    (RLC.retainedCanonCondDetStatement_of_untouched hRCDU₀)
  let hW5₀ := w5Statement_of_wire6_g7a h12₀ h13₀ h12₀ h13₀ h411₀ h51₀
    h411₀ h51₀ hCB₀ hDet₀ hRCDU₀ hFCD₀ hTrans hG3 hG7a hG8
  exact crosses_of_lt_of_remaining h77 hR hW5₀
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP₀))
    (Supp9.w0bStatement_of_lemma75 (lemma75Statement_of_open5 h411₀ h51₀ hcl₀))
    hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

end Wire

end InteractingSLE
