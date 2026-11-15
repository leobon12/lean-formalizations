/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm15Inputs3
import InteractingSLE.Spec.Sec7.Lemma72EMain
import InteractingSLE.Spec.Sec7.Lemma613
import InteractingSLE.Spec.Sec7.Lemma725Det
import InteractingSLE.Spec.Sec7.LocalExtNPost
import InteractingSLE.Spec.Sec7.LocalExtOMain
import InteractingSLE.Spec.Sec5.Prop55N
import InteractingSLE.Spec.Restart.CondDetG7
import InteractingSLE.Spec.Sec7.Lemma76EMain
import InteractingSLE.Spec.Sec7.Prop74BMain
import InteractingSLE.Spec.Sec7.Prop74BOrient
import InteractingSLE.Spec.Sec7.Aux97GermExt
import InteractingSLE.Spec.Supplement.RLCMain
import InteractingSLE.Spec.Supplement.W0b
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Exist.CanonicalMain

/-!
# Theorem 1.5 with the results landed since PROVE-WIRE3 plugged in

Packet PROVE-WIRE5 (no new mathematics). Theorems 1.2 and 1.3 enter only as the types of their frozen anchors
(`Exist.Theorem12Statement`, `Exist.Theorem13Statement`), at universe `u` and at universe `0`. Since PROVE-WIRE3:

* **R46.** `Restart.FlowCodeStatement` is refutable (PROVE-CONDDET), so the code route of PROVE-WIRE3 is replaced by the
  canonical codes: G7's retained kernel clock and the first-contact word kernel (R2′) follow from the word-measurable
  Theorem 1.2, Theorem 1.3 and the corrected conditional determinations
  (`Restart.retainedKernelClockStatement_of_param`, `Restart.firstContactWordKernelStatement_of_param`); the
  word-measurable Theorem 1.2 follows from Theorems 1.2–1.3 (`Exist.Param12.theorem12ParamStatement_of_thm12_thm13`);
* **Lemma 7.5** follows from Lemma 7.1's joint statement (Aux. lemma 54 and the restarted seed coupling are proved,
  PROVE-LOCEXT-N/O: `Aux50Hit.lemma75Statement_of_embeddedPair`), the joint statement from Lemma 7.1's fixed-time clause
  and the three-curve space's inputs (`Sec7.Lemma72E.lemma71JointStatement_of_clause`, PROVE-LEMMA72E), and those from
  Propositions 4.11 and 5.1 in chart `Q` (PROVE-SEC5-N, PROVE-LEMMA71J);
* **W0b** follows from Lemma 7.5 (`Supp9.w0bStatement_of_lemma75`, PROVE-G12D);
* **Lemma 7.6** follows from Theorems 1.2–1.3 and `Sec7.Lemma76CondDetHeightsStatement` ((R1), the right-side heights
  and (Det); `Sec7.lemma76Statement_of_param_heights`, PROVE-LEMMA76E);
* **Proposition 7.4's order** follows from Lemma 7.5, the §4.2 reference, Proposition 5.5, the fixed-chart Lemma 7.1
  and the pocket-chart orientation (`Sec7.Prop74B.prop74OrderStatement_of_fixedChart`, PROVE-PROP74B), the orientation
  being proved (`Sec7.Prop74B.pocketChartOrientationStatement`, PROVE-ORIENT);
* **Aux. lemma 97's germ identification** follows from Theorems 1.2–1.3 and the stopped seed extension for `κ < 4`
  (`Sec7.Aux97G.aux97GermIdentStatement_of_extend`, PROVE-AUX97G);
* **the retained local completion** follows from the joint-chart completion and the real-contact case
  (`RLC.retainedLocalCompletionStatement_of_chart`, PROVE-RLC-A);
* **the companion** `exists_isFlowLine` follows from Theorems 1.2–1.3 alone
  (`Exist.exists_isFlowLine_of_thm12_thm13_only`, PROVE-FLOWEXIST3).

Every theorem here is a conditional helper with a distinct name; none is a provider.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-! ### The narrowed inputs, at one universe -/

/-- **Lemma 7.1's joint statement** (`κ < 4`) from Propositions 4.11 and 5.1 in chart `Q` (the §4.2 reference,
Proposition 5.5 and Lemma 6.13) and Lemma 7.1's fixed-time pocket clause (PROVE-LEMMA72E). -/
theorem lemma71JointStatement_of_open5 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) :
    Sec7.Lemma72.Lemma71JointStatement.{u} :=
  Sec7.Lemma72E.lemma71JointStatement_of_clause (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)
    (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51)
    (Sec7.Lemma613.lemma613ContactStatement_of_prop55 (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)
      (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51)) hcl

/-- **Lemma 7.5** (`Theorem15.Lemma75Statement`) from Propositions 4.11 and 5.1 in chart `Q` and Lemma 7.1's fixed-time
pocket clause: Aux. lemma 54 (`LocalExt.stoppedSeedExtensionStatement`) and the restarted seed coupling
(`LocalExt.restartSeedCouplingStatement`) are proved. -/
theorem lemma75Statement_of_open5 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) :
    Theorem15.Lemma75Statement.{u} :=
  Aux50Hit.lemma75Statement_of_embeddedPair
    (prop73TraceStatement_of_joint3 (lemma71JointStatement_of_open5 h411 h51 hcl))
    (Sec7.Lemma72.embeddedPairStatement_of_joint (lemma71JointStatement_of_open5 h411 h51 hcl))
    (fun _ hκ _ => LocalExt.stoppedSeedExtensionStatement hκ) (fun _ hκ _ => LocalExt.restartSeedCouplingStatement hκ)

/-- **Lemma 7.6** from Theorems 1.2–1.3 at universe `0` (frozen types) and (R1) + right-side heights + (Det). -/
theorem lemma76Statement_of_open5 (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hD76 : Sec7.Lemma76CondDetHeightsStatement.{u}) : Sec7.Lemma76Statement.{u} :=
  Sec7.lemma76Statement_of_param_heights (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hD76

/-- **Lemma 7.7** from the inputs of Lemmas 7.5 and 7.6 (Aux. lemma 56 at first entrances proved). -/
theorem lemma77Statement_of_open5 (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) (hD76 : Sec7.Lemma76CondDetHeightsStatement.{u}) :
    Supp10.Lemma77Statement.{u} :=
  lemma77Statement_of_open3 (lemma76Statement_of_open5 h12₀ h13₀ hD76) (lemma75Statement_of_open5 h411 h51 hcl)

/-- **G7's retained kernel clock** from Theorems 1.2–1.3 at universe `0` (frozen types) and the corrected retained
conditional determination (PROVE-CONDDET; replaces the refutable code route, R46). -/
theorem retainedKernelClockStatement_of_open5 (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hRCD : Restart.RetainedCanonCondDetStatement.{u}) :
    Supp7.RetainedKernelClockStatement.{u} :=
  Restart.retainedKernelClockStatement_of_param (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀
    hRCD

/-- **Proposition 7.4's order** from Propositions 4.11 and 5.1 in chart `Q`, Lemma 7.1's fixed-time pocket clause (for
Lemma 7.5) and the fixed-chart Lemma 7.1 (the pocket-chart orientation is proved, PROVE-ORIENT). -/
theorem prop74OrderStatement_of_open5 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hcl : Sec7.Lemma72E.PocketClauseStatement.{u})
    (hfc : Sec7.Prop74B.Lemma71FixedChartStatement.{u}) :
    Sec7.Prop74OrderStatement.{u} :=
  Sec7.Prop74B.prop74OrderStatement_of_fixedChart (lemma75Statement_of_open5 h411 h51 hcl)
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)
    (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51) hfc
    Sec7.Prop74B.pocketChartOrientationStatement

/-- **Theorem W5's common-seed comparison** from Proposition 7.4's order (its inputs as above) and Aux. lemma 97's germ
identification (Theorems 1.2–1.3 at universe `u` and the stopped seed extension for `κ < 4`). -/
theorem w5CommonSeedStatement_of_open5 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) (hfc : Sec7.Prop74B.Lemma71FixedChartStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.StoppedSeedExtendStatement.{u} κ) :
    Supp9.W5CommonSeedStatement.{u} :=
  Supp9.w5CommonSeedStatement_of_germIdent (prop74OrderStatement_of_open5 h411 h51 hcl hfc)
    (Sec7.Aux97G.aux97GermIdentStatement_of_extend (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13
      hext)

/-- **The first-contact restart (limit form)** from the inputs of Lemmas 7.5–7.7, Theorems 1.2–1.3 at universe `0`
(frozen types) and the corrected first-contact conditional determination (Aux. lemmas 25 and 56 proved; R46). -/
theorem firstContactRestartLimStatement_of_open5 (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hcl : Sec7.Lemma72E.PocketClauseStatement.{u})
    (hD76 : Sec7.Lemma76CondDetHeightsStatement.{u}) (hFCD : Restart.FirstContactCanonCondDetStatement.{u}) :
    Theorem15D5.FirstContactRestartLimStatement.{u} :=
  WholeField.firstContactRestartLimStatement_of_lemmas Theorem15.aux25Statement (lemma75Statement_of_open5 h411 h51 hcl)
    (lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76)
    (Restart.firstContactWordKernelStatement_of_param (lemma75Statement_of_open5 h411 h51 hcl)
      (lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76)
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hFCD)

/-! ### The three clauses -/

/-- **Theorem 1.5 (i)** (`IsFlowLine.stays_right_of_lt`), provider shape (conditional helper; not the provider), from:
Theorems 1.2–1.3 (frozen types, at `u` and `0`); at universe `u`: Propositions 4.11 and 5.1 in chart `Q`, Lemma 7.1's
fixed-time pocket clause, the fixed-chart Lemma 7.1, the stopped seed extension for
`κ < 4`, the retained canonical conditional determination, the joint-chart completion and the real-contact completion;
at universe `0`: Propositions 4.11 and 5.1 in chart `Q`, the pocket clause and (R1) + heights + (Det) of Lemma 7.6. -/
theorem stays_right_of_lt_of_open5
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) (hfc : Sec7.Prop74B.Lemma71FixedChartStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.StoppedSeedExtendStatement.{u} κ)
    (hRCD : Restart.RetainedCanonCondDetStatement.{u}) (hCC : RLC.RetainedChartCompletionStatement.{u})
    (hRR : RLC.RetainedLocalCompletionRealStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hcl₀ : Sec7.Lemma72E.PocketClauseStatement.{0}) (hD76₀ : Sec7.Lemma76CondDetHeightsStatement.{0})
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
  have hRP := retainedKernelClockStatement_of_open5 h12₀ h13₀ hRCD
  stays_right_of_lt_of_remaining_w0b
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP))
    (Supp9.w0bStatement_of_lemma75 (lemma75Statement_of_open5 h411 h51 hcl))
    (lemma77Statement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hD76₀)
    (Supp7.jointRetainedPairStatement_of_kernelClock hRP) (RLC.retainedLocalCompletionStatement_of_chart hCC hRR)
    (w5CommonSeedStatement_of_open5 h12 h13 h411 h51 hcl hfc hext) hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (ii)** (`IsFlowLine.merges`), provider shape (conditional helper; not the provider), from: Theorems
1.2–1.3 at universe `0` (frozen types); at universe `u`: Propositions 4.11 and 5.1 in chart `Q`, Lemma 7.1's fixed-time
pocket clause, (R1) + heights + (Det) of Lemma 7.6 and the first-contact canonical conditional determination; at
universe `0`: Propositions 4.11 and 5.1 in chart `Q` and the pocket clause. -/
theorem merges_of_open5
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) (hD76 : Sec7.Lemma76CondDetHeightsStatement.{u})
    (hFCD : Restart.FirstContactCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hcl₀ : Sec7.Lemma72E.PocketClauseStatement.{0})
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
  merges_of_remaining (lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76)
    (Theorem15D5.firstContactRestartStatement_of_lim
      (firstContactRestartLimStatement_of_open5 h12₀ h13₀ h411 h51 hcl hD76 hFCD))
    (lemma75Statement_of_open5 h411 h51 hcl) (lemma75Statement_of_open5 h411₀ h51₀ hcl₀) hκ hκ4 b jumps hb hx hh
    hη₁ hη₂

/-- **Theorem 1.5 (iii)** (`IsFlowLine.crosses_of_lt`), provider shape (conditional helper; not the provider), from:
Theorems 1.2–1.3 at universe `0` (frozen types); at universe `u`: the inputs of clause (ii); at universe `0`: the inputs
of clause (i) (Propositions 4.11 and 5.1 in chart `Q`, the pocket clause, (R1) + heights + (Det), the fixed-chart
Lemma 7.1, the stopped seed extension, the retained canonical conditional determination, both completions). The
auto-parameters `hx`, `hθ`, `hθπ` come after `hη₁`, `hη₂` (PROVE-WIRE2's pitfall). -/
theorem crosses_of_lt_of_open5
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hcl : Sec7.Lemma72E.PocketClauseStatement.{u}) (hD76 : Sec7.Lemma76CondDetHeightsStatement.{u})
    (hFCD : Restart.FirstContactCanonCondDetStatement.{u})
    (h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0}) (h51₀ : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hcl₀ : Sec7.Lemma72E.PocketClauseStatement.{0}) (hD76₀ : Sec7.Lemma76CondDetHeightsStatement.{0})
    (hfc₀ : Sec7.Prop74B.Lemma71FixedChartStatement.{0})
    (hext₀ : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.StoppedSeedExtendStatement.{0} κ)
    (hRCD₀ : Restart.RetainedCanonCondDetStatement.{0}) (hCC₀ : RLC.RetainedChartCompletionStatement.{0})
    (hRR₀ : RLC.RetainedLocalCompletionRealStatement.{0})
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
  have hRP₀ := retainedKernelClockStatement_of_open5 h12₀ h13₀ hRCD₀
  crosses_of_lt_of_remaining_w0b (lemma77Statement_of_open5 h12₀ h13₀ h411 h51 hcl hD76)
    (firstContactRestartLimStatement_of_open5 h12₀ h13₀ h411 h51 hcl hD76 hFCD)
    (Supp7.g7GB7aFirstHitStatement_of_g7 (Supp7.g7RetainedPairStatement_of_kernelClock hRP₀))
    (Supp9.w0bStatement_of_lemma75 (lemma75Statement_of_open5 h411₀ h51₀ hcl₀))
    (lemma77Statement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hD76₀)
    (Supp7.jointRetainedPairStatement_of_kernelClock hRP₀) (RLC.retainedLocalCompletionStatement_of_chart hCC₀ hRR₀)
    (w5CommonSeedStatement_of_open5 h12₀ h13₀ h411₀ h51₀ hcl₀ hfc₀ hext₀) hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

/-! ### The companion `exists_isFlowLine` -/

/-- **Theorem 1.5's companion** (`exists_isFlowLine`), provider shape, from Theorems 1.2–1.3 alone (frozen types;
PROVE-FLOWEXIST3's `Exist.exists_isFlowLine_of_thm12_thm13_only`; conditional helper; not the provider). -/
theorem exists_isFlowLine_of_open5 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  Exist.exists_isFlowLine_of_thm12_thm13_only h12 h13 hκ hκ4 hb hh

end Wire

end InteractingSLE
