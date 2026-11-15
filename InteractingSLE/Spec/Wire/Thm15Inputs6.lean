/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm15Inputs5
import InteractingSLE.Spec.Supplement.RLCCMain
import InteractingSLE.Spec.Supplement.RLCBMain
import InteractingSLE.Spec.Supplement.RLCHG2aParts
import InteractingSLE.Spec.Supplement.RLCIOrderWire
import InteractingSLE.Spec.Sec7.Aux97GermPost
import InteractingSLE.Spec.Sec7.Lemma76FMain
import InteractingSLE.Spec.Sec7.Lemma71TWire
import InteractingSLE.Spec.Supplement.G12LowWire

/-!
# Theorem 1.5 providers from the latest remaining inputs

Aux. 97's germ identification uses Theorems 1.2–1.3 directly. Lemma 7.6's (R1) input is built from its chart-boundary
and deterministic inputs; Lemma 7.1's pocket and fixed-chart clauses follow from Proposition 4.11. Theorem W5 uses the
localized real-contact chart input and derives G2a from transience and RLC-I's order reduction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- Lemma 7.6's conditional-law input from Lemma 7.5, its chart boundary input and (Det). -/
theorem lemma76CondDetHeightsStatement_of_wire6 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hCB : Sec7.Lemma76ChartBoundaryStatement.{u})
    (hDet : Sec7.Lemma76DetStatement.{u}) : Sec7.Lemma76CondDetHeightsStatement.{u} := by
  let href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  let hcl := Sec7.Lemma71T.pocketClauseStatement href
  exact Sec7.lemma76CondDetHeightsStatement_of_chartBoundary (lemma75Statement_of_open5 h411 h51 hcl) hCB hDet

/-- Theorem W5 from the current inputs, including the localized real-contact chart statement. -/
theorem w5Statement_of_chartReal_wire6 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hCB₀ : Sec7.Lemma76ChartBoundaryStatement.{0}) (hDet₀ : Sec7.Lemma76DetStatement.{0})
    (hRCD : Restart.RetainedCanonCondDetStatement.{u})
    (hFCD₀ : Restart.FirstContactCanonCondDetStatement.{0})
    (hTrans : RLC.G2aTransienceStatement.{0}) (hG3 : RLC.G3ChartComparisonStatement.{0})
    (hChart : RLC.RetainedChartRealCompletionStatement.{u}) : Theorem15.W5Statement.{u} := by
  let href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  let href₀ := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411₀
  let hcl := Sec7.Lemma71T.pocketClauseStatement href
  let hcl₀ := Sec7.Lemma71T.pocketClauseStatement href₀
  let hfc := Sec7.Lemma71T.lemma71FixedChartStatement href
  let hD76₀ := lemma76CondDetHeightsStatement_of_wire6 h411₀ h51₀ hCB₀ hDet₀
  let h77₀ := lemma77Statement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hD76₀
  let hL75 := lemma75Statement_of_open5 h411 h51 hcl
  let hRP := retainedKernelClockStatement_of_open5 h12₀ h13₀ hRCD
  let hJ := Supp7.jointRetainedPairStatement_of_kernelClock hRP
  let hParts := RLC.g2aPartsStatement_of_transience hTrans
  let hG2a := RLC.g2aReferenceStatement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hD76₀ hFCD₀ h411₀ h51₀ hParts
  let hCS := w5CommonSeedStatement_of_open5 h12 h13 h411 h51 hcl hfc
    (fun _ hκ _ => LocalExt.stoppedSeedExtendStatement hκ)
  exact RLC.w5Statement_of_chartReal_param Theorem15.aux25Statement Supp7.w0aStatement
    (Supp9.w0bStatement_of_lemma75 hL75) h77₀ hJ hCS (RLC.g2ReferenceStatement_of_g2a hG2a) hG3
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hRCD hChart

/-! ### The three clauses -/

/-- Theorem 1.5 (i), using the current W5 chart-real completion route. -/
theorem stays_right_of_lt_of_wire6
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hRCD : Restart.RetainedCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hCB₀ : Sec7.Lemma76ChartBoundaryStatement.{0}) (hDet₀ : Sec7.Lemma76DetStatement.{0})
    (hFCD₀ : Restart.FirstContactCanonCondDetStatement.{0})
    (hTrans : RLC.G2aTransienceStatement.{0}) (hG3 : RLC.G3ChartComparisonStatement.{0})
    (hChart : RLC.RetainedChartRealCompletionStatement.{u})
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
  let href₀ := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411₀
  let hcl := Sec7.Lemma71T.pocketClauseStatement href
  let hcl₀ := Sec7.Lemma71T.pocketClauseStatement href₀
  let hD76₀ := lemma76CondDetHeightsStatement_of_wire6 h411₀ h51₀ hCB₀ hDet₀
  let h77₀ := lemma77Statement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hD76₀
  let hL75 := lemma75Statement_of_open5 h411 h51 hcl
  let hW5 := w5Statement_of_chartReal_wire6 h12 h13 h12₀ h13₀ h411 h51
    h411₀ h51₀ hCB₀ hDet₀ hRCD hFCD₀ hTrans hG3 hChart
  let hRP := retainedKernelClockStatement_of_open5 h12₀ h13₀ hRCD
  exact stays_right_of_lt_of_remaining hW5
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP))
    (Supp9.w0bStatement_of_lemma75 hL75) hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- Theorem 1.5 (ii), with Lemma 7.6 discharged through its chart-boundary route. -/
theorem merges_of_wire6
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hCB : Sec7.Lemma76ChartBoundaryStatement.{u}) (hDet : Sec7.Lemma76DetStatement.{u})
    (hFCD : Restart.FirstContactCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x₁ x₂ θ : ℝ} (hx : x₂ ≤ x₁ := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁ := by assumption)
    (hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂ := by assumption) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t :=
  let href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  let href₀ := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411₀
  let hcl := Sec7.Lemma71T.pocketClauseStatement href
  let hcl₀ := Sec7.Lemma71T.pocketClauseStatement href₀
  merges_of_open5 h12₀ h13₀ h411 h51 hcl (lemma76CondDetHeightsStatement_of_wire6 h411 h51 hCB hDet)
    hFCD h411₀ h51₀ hcl₀ hκ hκ4 hb hx hh hη₁ hη₂

/-! ### Clause (iii) and the companion -/

/-- Theorem 1.5 (iii), using the localized chart-real W5 route at universe `0`. -/
theorem crosses_of_lt_of_wire6
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hCB : Sec7.Lemma76ChartBoundaryStatement.{u}) (hDet : Sec7.Lemma76DetStatement.{u})
    (hFCD : Restart.FirstContactCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hCB₀ : Sec7.Lemma76ChartBoundaryStatement.{0}) (hDet₀ : Sec7.Lemma76DetStatement.{0})
    (hRCD₀ : Restart.RetainedCanonCondDetStatement.{0})
    (hFCD₀ : Restart.FirstContactCanonCondDetStatement.{0})
    (hTrans : RLC.G2aTransienceStatement.{0}) (hG3 : RLC.G3ChartComparisonStatement.{0})
    (hChart₀ : RLC.RetainedChartRealCompletionStatement.{0})
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
  let hfc₀ := Sec7.Lemma71T.lemma71FixedChartStatement href₀
  let hD76 := lemma76CondDetHeightsStatement_of_wire6 h411 h51 hCB hDet
  let hD76₀ := lemma76CondDetHeightsStatement_of_wire6 h411₀ h51₀ hCB₀ hDet₀
  let h77 := lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76
  let hR := firstContactRestartLimStatement_of_open5 h12₀ h13₀ h411 h51 hcl hD76 hFCD
  let hRP₀ := retainedKernelClockStatement_of_open5 h12₀ h13₀ hRCD₀
  let hW5₀ := w5Statement_of_chartReal_wire6 h12₀ h13₀ h12₀ h13₀ h411₀ h51₀
    h411₀ h51₀ hCB₀ hDet₀ hRCD₀ hFCD₀ hTrans hG3 hChart₀
  exact crosses_of_lt_of_remaining h77 hR hW5₀
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP₀))
    (Supp9.w0bStatement_of_lemma75 (lemma75Statement_of_open5 h411₀ h51₀ hcl₀))
    hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

/-- The companion of Theorem 1.5. -/
theorem exists_isFlowLine_of_wire6 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  exists_isFlowLine_of_open5 h12 h13 hκ hκ4 hb hh

end Wire

end InteractingSLE
