/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12Inputs3
import InteractingSLE.Spec.Wire.Thm13Inputs3
import InteractingSLE.Spec.Wire.Thm15Inputs2
import InteractingSLE.Spec.Supplement.G7RestartInterface
import InteractingSLE.Spec.Supplement.G12LowWire
import InteractingSLE.Spec.Supplement.GB7aCmp
import InteractingSLE.Spec.Restart.KernelG7
import InteractingSLE.Spec.Restart.KernelFC
import InteractingSLE.Spec.Coupling.WholeField9Entr
import InteractingSLE.Spec.Sec7.ReverseArcAux70

/-!
# Theorem 1.5 with the results landed since PROVE-WIRE2 plugged in

Packet PROVE-WIRE3 (no new mathematics). PROVE-WIRE2 left the three clauses of Theorem 1.5 with fourteen distinct open
statements and the companion `exists_isFlowLine` with eighteen. Since then:

* Aux. lemma 56 at first entrances is a theorem (`WholeField.retainedRangeEntranceStatement`, PROVE-WHOLEFIELD9), so
  Lemma 7.7 follows from Lemma 7.6 and Lemma 7.5 alone (`Sec7.lemma77Statement_of_lemma76_of_lemma75`, PROVE-LEMMA76B,
  with the side heights of PROVE-SIDEHEIGHT inside): Aux. lemma 70 (`h70`) is no longer an input of any clause
  (it follows from Lemma 7.5 alone, `aux70Statement_of_open3`);
* the retained-range kernel (`hKr`) is no longer used: the first-contact restart comes from Aux. 25, Lemmas 7.5 and 7.7
  and the first-contact word kernel (`WholeField.firstContactRestartLimStatement_of_lemmas`);
* the first-contact word kernel (`hW`) follows from Lemmas 7.5, 7.7, the flow-code statement and the first-contact
  conditional determination (`Restart.firstContactWordKernelStatement_of_condDet`, PROVE-RESTARTKERNEL);
* Lemma G7 and the joint retained pair (`hG7`, `hJ`) follow from the retained kernel-clock statement
  (`Supp7.g7RetainedPairStatement_of_kernelClock`, `jointRetainedPairStatement_of_kernelClock`, PROVE-G7B), and that
  from the flow-code statement and the retained conditional determination
  (`Restart.retainedKernelClockStatement_of_condDet`, PROVE-RESTARTKERNEL);
* Lemma G12 is no longer an input: it enters clauses (i)/(iii) only through Corollary W0a, which is now unconditional
  (`Supp7.w0aStatement`; `Wire.stays_right_of_lt_of_remaining_w0b`, `crosses_of_lt_of_remaining_w0b`, PROVE-G12C),
  and GB7a is proved (`Supp7.g7GB7aFirstHitStatement_of_g7`, PROVE-GB7A3);
* Lemma 7.5 (`hL75`, unowned in PROVE-WIRE2) follows from Theorem 1.2's open inputs for `0 < κ < 4` through the
  Lemma 7.5 bridge (`Wire.lemma75Statement_of_open3`; PROVE-PROP73D, PROVE-PROP73R, PROVE-LEMMA72).

Each clause wrapper takes Lemma 7.5's five inputs (`hJ`, `h50`, `hPre`, `hLoc`, `hdl`, restricted to `κ < 4`) in
place of `hL75`. The companion takes the union of the open inputs of Theorems 1.2 and 1.3 (`Thm12Inputs3`,
`Thm13Inputs3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-! ### The narrowed inputs -/

/-- **Lemma 7.7** from Lemma 7.6 and Lemma 7.5 (Aux. lemma 56 at first entrances proved). -/
theorem lemma77Statement_of_open3 (h76 : Sec7.Lemma76Statement.{u}) (hL75 : Theorem15.Lemma75Statement.{u}) :
    Supp10.Lemma77Statement.{u} :=
  Sec7.lemma77Statement_of_lemma76_of_lemma75 h76 hL75 WholeField.retainedRangeEntranceStatement

/-- **Aux. lemma 70** from Lemma 7.5 alone (Aux. lemma 56 at first entrances proved; PROVE-LEMMA76B). No clause wrapper
below needs it any more. -/
theorem aux70Statement_of_open3 (hL75 : Theorem15.Lemma75Statement.{u}) : Sec7.Aux70Statement.{u} :=
  Sec7.aux70Statement_of_lemma75 hL75 WholeField.retainedRangeEntranceStatement

/-- **The first-contact restart (limit form)** from Lemmas 7.5 and 7.6, the flow-code statement and the first-contact
conditional determination (Aux. lemmas 25 and 56 proved). -/
theorem firstContactRestartLimStatement_of_open3 (h76 : Sec7.Lemma76Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hFC : Restart.FlowCodeStatement)
    (hFCD : Restart.FirstContactCondDetStatement.{u}) : Theorem15D5.FirstContactRestartLimStatement.{u} :=
  WholeField.firstContactRestartLimStatement_of_lemmas Theorem15.aux25Statement hL75
    (lemma77Statement_of_open3 h76 hL75)
    (Restart.firstContactWordKernelStatement_of_condDet hL75 (lemma77Statement_of_open3 h76 hL75) hFC hFCD)

/-! ### The three clauses -/

/-- **Theorem 1.5 (i)** (`IsFlowLine.stays_right_of_lt`), provider shape, from: the flow-code statement, the retained
conditional determination, W0b, the retained local completion, Proposition 7.4's order and
Aux. lemma 97's germ identification (universe `u`), and Lemma 7.6 and Lemma 7.5's five inputs at universe `0`
(conditional helper; not the provider). -/
theorem stays_right_of_lt_of_open3
    (hFC : Restart.FlowCodeStatement) (hRCD : Restart.RetainedCondDetStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (hL : Supp9D.RetainedLocalCompletionStatement.{u})
    (h74 : Sec7.Prop74OrderStatement.{u}) (hg : Sec7.Aux97GermIdentStatement.{u})
    (h76₀ : Sec7.Lemma76Statement.{0})
    (hJ₀ : Sec7.Lemma72.Lemma71JointStatement.{0})
    (h50₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{0, 0} κ rL rR)
    (hPre₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtPreStopStatement.{0} κ)
    (hLoc₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtLocalityStatement.{0} κ)
    (hdl₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartDrivingLocalityInput.{0} κ)
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
        ¬ IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  have hRP := Restart.retainedKernelClockStatement_of_condDet hFC hRCD
  stays_right_of_lt_of_remaining_w0b
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP)) hW0b (lemma77Statement_of_open3 h76₀ (lemma75Statement_of_open3 hJ₀ h50₀ hPre₀ hLoc₀ hdl₀))
    (Supp7.jointRetainedPairStatement_of_kernelClock hRP) hL
    (Supp9.w5CommonSeedStatement_of_germIdent h74 hg) hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (ii)** (`IsFlowLine.merges`), provider shape, from Lemma 7.6, the flow-code statement, the
first-contact conditional determination and Lemma 7.5's five inputs (universe `u`), and Lemma 7.5's five inputs at
universe `0` (conditional helper; not the provider). -/
theorem merges_of_open3
    (h76 : Sec7.Lemma76Statement.{u}) (hFC : Restart.FlowCodeStatement)
    (hFCD : Restart.FirstContactCondDetStatement.{u})
    (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hPre : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtPreStopStatement.{u} κ)
    (hLoc : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtLocalityStatement.{u} κ)
    (hdl : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartDrivingLocalityInput.{u} κ)
    (hJ₀ : Sec7.Lemma72.Lemma71JointStatement.{0})
    (h50₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{0, 0} κ rL rR)
    (hPre₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtPreStopStatement.{0} κ)
    (hLoc₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtLocalityStatement.{0} κ)
    (hdl₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartDrivingLocalityInput.{0} κ)
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
  have hL75 := lemma75Statement_of_open3 hJ h50 hPre hLoc hdl
  merges_of_remaining (lemma77Statement_of_open3 h76 hL75)
    (Theorem15D5.firstContactRestartStatement_of_lim (firstContactRestartLimStatement_of_open3 h76 hL75 hFC hFCD))
    hL75 (lemma75Statement_of_open3 hJ₀ h50₀ hPre₀ hLoc₀ hdl₀) hκ hκ4 b jumps hb hx hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** (`IsFlowLine.crosses_of_lt`), provider shape, from Lemma 7.6, the flow-code statement, the
first-contact conditional determination and Lemma 7.5's five inputs (universe `u`), and clause (i)'s inputs at universe
`0` (conditional helper; not the provider). The auto-parameters `hx`, `hθ`, `hθπ` come after `hη₁`, `hη₂` (PROVE-WIRE2's
pitfall: `x₁`, `x₂` do not occur in the conclusion). -/
theorem crosses_of_lt_of_open3
    (h76 : Sec7.Lemma76Statement.{u}) (hFC : Restart.FlowCodeStatement)
    (hFCD : Restart.FirstContactCondDetStatement.{u})
    (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hPre : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtPreStopStatement.{u} κ)
    (hLoc : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtLocalityStatement.{u} κ)
    (hdl : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartDrivingLocalityInput.{u} κ)
    (hRCD₀ : Restart.RetainedCondDetStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
    (hL₀ : Supp9D.RetainedLocalCompletionStatement.{0})
    (h74₀ : Sec7.Prop74OrderStatement.{0}) (hg₀ : Sec7.Aux97GermIdentStatement.{0})
    (h76₀ : Sec7.Lemma76Statement.{0})
    (hJ₀ : Sec7.Lemma72.Lemma71JointStatement.{0})
    (h50₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{0, 0} κ rL rR)
    (hPre₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtPreStopStatement.{0} κ)
    (hLoc₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtLocalityStatement.{0} κ)
    (hdl₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartDrivingLocalityInput.{0} κ)
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
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) :=
  have hL75 := lemma75Statement_of_open3 hJ h50 hPre hLoc hdl
  have hRP₀ := Restart.retainedKernelClockStatement_of_condDet hFC hRCD₀
  crosses_of_lt_of_remaining_w0b (lemma77Statement_of_open3 h76 hL75)
    (firstContactRestartLimStatement_of_open3 h76 hL75 hFC hFCD)
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP₀)) hW0b₀
    (lemma77Statement_of_open3 h76₀ (lemma75Statement_of_open3 hJ₀ h50₀ hPre₀ hLoc₀ hdl₀))
    (Supp7.jointRetainedPairStatement_of_kernelClock hRP₀) hL₀
    (Supp9.w5CommonSeedStatement_of_germIdent h74₀ hg₀) hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

/-! ### The companion `exists_isFlowLine` -/

/-- **Theorem 1.5's companion** (`exists_isFlowLine`), provider shape, from the open inputs of Theorems 1.2 and 1.3
(`theorem12Statement_of_open3`, `theorem13Statement_of_open3`; seventeen distinct names, `hhit`, `hR7`, `hPW` shared)
through PROVE-FLOWEXIST3's `Exist.exists_isFlowLine_of_thm12_thm13_only` (conditional helper; not the provider). -/
theorem exists_isFlowLine_of_open3
    -- shared by Theorems 1.2 and 1.3
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    -- Theorem 1.2 only
    (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hcon : WangWu.ReverseTipContactStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (h50R : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      Aux50.HasTraceStopKernel.{0, u} κ rL rR)
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPre : ∀ κ : ℝ, 0 < κ → LocalExt.ExtPreStopStatement.{u} κ)
    (hLoc : ∀ κ : ℝ, 0 < κ → LocalExt.ExtLocalityStatement.{u} κ)
    (hdl : ∀ κ : ℝ, 0 < κ → LocalExt.RestartDrivingLocalityInput.{u} κ)
    -- Theorem 1.3 only
    (hPC : Sec7.Lemma71C.Lemma71PocketChartStatement.{0})
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi3.LowCritStatement.{u} κ (-2))
    (hlow : ∀ κ : ℝ, 4 ≤ κ → Sec7.TrialsHi3.LowCritStatement.{u} κ (κ / 2 - 4))
    (h8 : ∀ κ : ℝ, 4 < κ → Sec7.TrialsHi3.LP8CritStatement.{u} κ)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  Exist.exists_isFlowLine_of_thm12_thm13_only
    (theorem12Statement_of_open3 hJ h50 hcon hneg hhit hR7 h50R h725d hPW hPre hLoc hdl)
    (theorem13Statement_of_open3 hPC hmid hlow h8 hhit hR7 hPW hcol) hκ hκ4 hb hh

end Wire

end InteractingSLE
