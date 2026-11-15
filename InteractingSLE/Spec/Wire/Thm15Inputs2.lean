/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12Inputs2
import InteractingSLE.Spec.Wire.Theorem15
import InteractingSLE.Spec.Supplement.G7Interface
import InteractingSLE.Spec.Supplement.G12Bridge
import InteractingSLE.Spec.Sec7.Lemma77RealLens
import InteractingSLE.Spec.Sec7.Aux97ProofGerm
import InteractingSLE.Spec.Coupling.WholeField8Entr
import InteractingSLE.Spec.Exist.CanonicalMain

/-!
# Theorem 1.5 and its companion `exists_isFlowLine` with the results landed since PROVE-WIRE1 plugged in

Packet PROVE-WIRE2 (no new mathematics). PROVE-WIRE1 left Theorem 1.5's clauses with nine distinct open statements
(`Wire.stays_right_of_lt_of_remaining_g12`, `Wire.merges_of_remaining`,
`Wire.crosses_of_lt_of_remaining_g12`). Since then:

* Lemma GB7a is unconditional and interface 4 (`Theorem15D5.G7GB7aFirstHitStatement`) needs Lemma G7 only
  (PROVE-GB7A3; the clause wrappers `Supp7.stays_right_of_lt_of_g7_g12`, `Supp7.crosses_of_lt_of_g7_g12`);
* Lemma 7.7 follows from Lemma 7.6 and Aux. lemma 70 (`Sec7.lemma77Statement_of_aux70_of_lemma76`, PROVE-LEMMA77-B);
* W5's common seed follows from Proposition 7.4's order statement and the germ identification of Aux. lemma 97
  (`Supp9.w5CommonSeedStatement_of_germIdent`, PROVE-AUX97-B);
* `Supp7.G12EvolStatement` follows from Lemma G12's remainder (`Supp7.G12.g12EvolStatement_of_remainder`, PROVE-G12);
* the first-contact restart (limit form) follows from Aux. lemma 25 (proved), Lemma 7.5, Lemma 7.7, the general-`κ`
  retained-range kernel and the first-contact word kernel (`WholeField.firstContactRestartLimStatement_of_kernel`,
  PROVE-WHOLEFIELD8, through Aux. 56 at first entrances);
* the frozen companion `exists_isFlowLine` follows from the frozen Theorems 1.2 and 1.3 alone
  (`Exist.exists_isFlowLine_of_thm12_thm13_only`, PROVE-FLOWEXIST3), here fed by this packet's wrappers
  `Wire.exists_measurable_lifetime_trace_eq_comp_field_of_remaining2` and
  `Wire.ae_exists_isGeneratingTrace_of_remaining2`.

Each wrapper has exactly the conclusion of its frozen anchor in the provider shape (all of the anchor's arguments
implicit, its hypotheses auto-parameters). They are conditional helpers, not providers. Theorem 1.5 is claimed only with
its three clauses and `exists_isFlowLine` (ruling R26).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-! ### The narrowed inputs -/

/-- **Lemma 7.7** from Aux. lemma 70 and Lemma 7.6 (PROVE-LEMMA77-B). -/
theorem lemma77Statement_of_remaining2 (h70 : Sec7.Aux70Statement.{u}) (h76 : Sec7.Lemma76Statement.{u}) :
    Supp10.Lemma77Statement.{u} :=
  Sec7.lemma77Statement_of_aux70_of_lemma76 h70 h76

/-- **The first-contact restart (limit form)** from Aux. lemma 70, Lemma 7.6, Lemma 7.5, the retained-range kernel and
the first-contact word kernel (Aux. lemma 25 proved). -/
theorem firstContactRestartLimStatement_of_remaining2 (h70 : Sec7.Aux70Statement.{u})
    (h76 : Sec7.Lemma76Statement.{u}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hK : WholeField.RetainedRangeKernelStatement.{u}) (hW : Restart.FirstContactWordKernelStatement.{u}) :
    Theorem15D5.FirstContactRestartLimStatement.{u} :=
  WholeField.firstContactRestartLimStatement_of_kernel Theorem15.aux25Statement hL75
    (lemma77Statement_of_remaining2 h70 h76) hK hW

/-! ### The three clauses -/

/-- **Theorem 1.5 (i)** (`IsFlowLine.stays_right_of_lt`), provider shape, from the remaining named inputs: Lemma G7,
W0b, Lemma G12's remainder, the joint retained pair, the retained local completion, Proposition 7.4's order and the
germ identification of Aux. lemma 97 (universe `u`), and Aux. lemma 70 and Lemma 7.6 at universe `0` (conditional
helper; not the provider). -/
theorem stays_right_of_lt_of_remaining2
    (hG7 : Supp7.G7RetainedPairStatement.{u}) (hW0b : Supp9.W0bStatement.{u})
    (hG12 : Supp7.G12.G12RemainderStatement.{u})
    (hJ : Supp9D.JointRetainedPairStatement.{u}) (hL : Supp9D.RetainedLocalCompletionStatement.{u})
    (h74 : Sec7.Prop74OrderStatement.{u}) (hg : Sec7.Aux97GermIdentStatement.{u})
    (h70₀ : Sec7.Aux70Statement.{0}) (h76₀ : Sec7.Lemma76Statement.{0})
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
  Supp7.stays_right_of_lt_of_g7_g12 hG7 hW0b (Supp7.G12.g12EvolStatement_of_remainder hG12)
    (lemma77Statement_of_remaining2 h70₀ h76₀) hJ hL (Supp9.w5CommonSeedStatement_of_germIdent h74 hg)
    hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂

/-- **Theorem 1.5 (ii)** (`IsFlowLine.merges`), provider shape, from Aux. lemma 70, Lemma 7.6, Lemma 7.5, the
retained-range kernel and the first-contact word kernel (universe `u`), and Lemma 7.5 at universe `0` (conditional
helper; not the provider). -/
theorem merges_of_remaining2
    (h70 : Sec7.Aux70Statement.{u}) (h76 : Sec7.Lemma76Statement.{u}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hK : WholeField.RetainedRangeKernelStatement.{u}) (hW : Restart.FirstContactWordKernelStatement.{u})
    (hL75₀ : Theorem15.Lemma75Statement.{0})
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
  merges_of_remaining (lemma77Statement_of_remaining2 h70 h76)
    (Theorem15D5.firstContactRestartStatement_of_lim
      (firstContactRestartLimStatement_of_remaining2 h70 h76 hL75 hK hW)) hL75 hL75₀
    hκ hκ4 b jumps hb hx hh hη₁ hη₂

/-- **Theorem 1.5 (iii)** (`IsFlowLine.crosses_of_lt`), provider shape, from Aux. lemma 70, Lemma 7.6, Lemma 7.5, the
retained-range kernel and the first-contact word kernel (universe `u`), and clause (i)'s nine inputs at universe `0`
(conditional helper; not the provider). The auto-parameters `hx`, `hθ`, `hθπ` come after `hη₁`, `hη₂`: `x₁`, `x₂` do not
occur in the conclusion, and `hx := by assumption` placed first would match `hθπ`. -/
theorem crosses_of_lt_of_remaining2
    (h70 : Sec7.Aux70Statement.{u}) (h76 : Sec7.Lemma76Statement.{u}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hK : WholeField.RetainedRangeKernelStatement.{u}) (hW : Restart.FirstContactWordKernelStatement.{u})
    (hG7₀ : Supp7.G7RetainedPairStatement.{0}) (hW0b₀ : Supp9.W0bStatement.{0})
    (hG12₀ : Supp7.G12.G12RemainderStatement.{0})
    (hJ₀ : Supp9D.JointRetainedPairStatement.{0}) (hL₀ : Supp9D.RetainedLocalCompletionStatement.{0})
    (h74₀ : Sec7.Prop74OrderStatement.{0}) (hg₀ : Sec7.Aux97GermIdentStatement.{0})
    (h70₀ : Sec7.Aux70Statement.{0}) (h76₀ : Sec7.Lemma76Statement.{0})
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
  Supp7.crosses_of_lt_of_g7_g12 (lemma77Statement_of_remaining2 h70 h76)
    (firstContactRestartLimStatement_of_remaining2 h70 h76 hL75 hK hW) hG7₀ hW0b₀
    (Supp7.G12.g12EvolStatement_of_remainder hG12₀) (lemma77Statement_of_remaining2 h70₀ h76₀) hJ₀ hL₀
    (Supp9.w5CommonSeedStatement_of_germIdent h74₀ hg₀) hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂

/-! ### The companion `exists_isFlowLine` -/

/-- **Theorem 1.5's companion** (`exists_isFlowLine`), provider shape, from the inputs of this packet's Theorem 1.2 and
Theorem 1.3 wrappers (eighteen distinct named inputs: the ten of
`exists_measurable_lifetime_trace_eq_comp_field_of_remaining2` and the twelve of
`ae_exists_isGeneratingTrace_of_remaining2`, four shared) through PROVE-FLOWEXIST3's
`Exist.exists_isFlowLine_of_thm12_thm13_only` (conditional helper; not the provider). -/
theorem exists_isFlowLine_of_remaining2
    -- shared by Theorems 1.2 and 1.3
    (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    -- Theorem 1.2 only
    (h73d : Determination.Prop73DeterminationStatement.{u})
    (hdet4 : ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hK : R7.R7FieldKernelStatement.{0, u}) (h725d : LP.Lemma725DeterminationStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → LocalExt.StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → LocalExt.RestartSeedCouplingStatement.{u} κ)
    -- Theorem 1.3 only
    (h99 : ∀ κ : ℝ, 0 < κ → Sec7.Aux99StoppedStatement.{u} κ)
    (hmid : ∀ κ : ℝ, 0 < κ → κ < 4 → Sec7.TrialsHi2.HighTrialMidStatement.{u} κ)
    (h1s : Sec7.OneSidedPrefixStatement.{u})
    (hlow : ∀ κ : ℝ, 4 ≤ κ → Sec7.TrialsHi.HighTrialLowStatement.{u} κ)
    (h9 : ∀ κ : ℝ, 4 ≤ κ → Sec7.LP9PrefixStatement.{u} κ)
    (h8T : ∀ κ : ℝ, 4 < κ → Sec7.TrialsHi.LP8TrialStatement.{u} κ)
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    (hRS : LP.LP4RightSwallowStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  Exist.exists_isFlowLine_of_thm12_thm13_only
    (by
      intro _ hκ' _ _ _ _ _ _ hF' _ _ _ _ _ _ _ _ _ _ _ hcoup
      exact exists_measurable_lifetime_trace_eq_comp_field_of_remaining2 hP h73d hdet4 hhit hR7 hK h725d hPW hext
        hrs hκ' hF' hcoup)
    (by
      intro _ ha _ _ _ _ _ _ hF' _ _ _ _ _ _ _ _ _ _ hE
      exact ae_exists_isGeneratingTrace_of_remaining2 hP h99 hmid h1s hhit hlow h9 h8T hR7 hPW hcol hRS ha hF' hE)
    hκ hκ4 hb hh

end Wire

end InteractingSLE
