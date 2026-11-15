/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.StrongCrossChart
import InteractingSLE.Spec.Seal.Final
import InteractingSLE.Spec.Supplement.W0b
import InteractingSLE.Spec.Restart.FCThresholdDriverPremises
import InteractingSLE.Spec.Restart.FCKerDPath2
import InteractingSLE.Spec.Restart.FCKerLawC
import InteractingSLE.Spec.Restart.CondDetG7
import InteractingSLE.Spec.Sec7.Lemma76R
import InteractingSLE.Spec.Sec7.InteractionProbLemma77
import InteractingSLE.Spec.Wire.T15AsmLeaves
import InteractingSLE.Spec.Wire.Thm15Inputs3
import InteractingSLE.Spec.Wire.Thm1415CurrentStatements
import InteractingSLE.Spec.Coupling.WholeField9Entr
import InteractingSLE.Spec.Sec5.Aux61CptThm
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Sec4.Aux25Term

/-!
# Audit fix (crossing): the strengthened Theorem 1.5 (iii)

Packet PROVE-AF-CROSS (external audit of 2026-11-15, priority 1, §2.2, pp. 6–7). The frozen Theorem 1.5 (iii),
`IsFlowLine.crosses_of_lt`, concludes `CrossesFromRightAt` at the first contact. That predicate asks only that every pair
of strict outgoing prefixes have ordered proper completions in the active chart, which identical curves satisfy, so it
does not exclude merging after the contact (the audit's vertical-ray and quarter-circle diagnostics). The paper says
the first flow line **crosses** the second upon intersecting and never crosses back (Theorem 1.5 (iii), p. 30;
Proposition 7.12, p. 141); the specification's Theorem 7.12C (p. 542) states the missing part: "They have no common
nontrivial open outgoing arc".

## Main results

* **`StrongCrossStatement`**, **`strongCrossStatement_holds`**: the frozen Theorem 1.5 (iii) with the same hypotheses,
  the frozen crossing conclusion and, at the same first contact `(s₀, t₀)`, no open arc of either outgoing available
  path on the other outgoing available path; the frozen critical-angle clause unchanged.
* `strongCross_not_agreeAsCurvesAfter`: what the new clause rules out — almost surely the flow lines do not merge
  (`¬ AgreeAsCurvesAfter`) at that first contact. The deterministic step is
  `Cross.not_agreeAsCurvesAfter_of_noCommonOutgoingArc`.
* `noCommonOutgoingArc_upon_availableContact`: the new clause at the first contact forced by any available contact
  (real or interior), for use with the contact-scope fix.

## Route

The first conjuncts are the frozen anchor's, through its sealed provider `Seal.Final.IsFlowLine_crosses_of_lt`. The new
clause is `Cross.noCommonOutgoingArcStatement_of_inputs` (W0b applied to the conditional outgoing flow lines in the
first-contact chart, transported through the chart and the increasing clocks), closed by the inputs of the sealed
Theorem 1.5 route: Lemma 7.7 and the first-contact restart carrier with the active prime end (from Theorems 1.2–1.3,
`lemma77_restartLim_closed`), W5 on the canonical space (the sealed Theorem 1.5 (i)), and W0b from Lemma 7.5
(`Supp9.w0bStatement_of_lemma75`). Baire's theorem turns strict outgoing prefixes into whole outgoing paths
(`Cross.noCommonOutgoingArc_of_prefix`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace AuditFix

/-! ### The closed inputs -/

namespace Cross

/-- **Lemma 7.7 and the first-contact restart carrier with the active prime end, closed.** The terms of the sealed
Theorem 1.5 route (`Wire.theorem15Statement_current` with the corrected first-contact kernels of
`Wire.theorem15Statement_nowC`), with Theorems 1.2–1.3 from the proved fibre covers. -/
theorem lemma77_restartLim_closed :
    Supp10.Lemma77Statement.{u} ∧ Theorem15D5.FirstContactRestartLimStatement.{u} := by
  have h12 : Exist.Theorem12Statement.{u} := Sec5.Aux61Cpt.theorem12Statement_of_cptCover
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover
  have h12₀ : Exist.Theorem12Statement.{0} := Sec5.Aux61Cpt.theorem12Statement_of_cptCover
  have h13₀ : Exist.Theorem13Statement.{0} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have h75 : Theorem15.Lemma75Statement.{u} := Restart.FCPlumb.lemma75Statement_of_thm12_thm13 h12 h13
  have h76 : Sec7.Lemma76Statement.{u} :=
    Sec7.lemma76Statement_of_detR h12p₀ h13₀ h75 (Wire.T15Asm.lemma76DetRStatement_of_lemma75 h75 h13₀)
  have h77 : Supp10.Lemma77Statement.{u} := Wire.lemma77Statement_of_open3 h76 h75
  have hFC := Restart.FCPlumb.firstContactCanonCondDetStatement_of_forwardKernelsC_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76
    (Restart.FCPlumb.firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76' h12 h13 h76)
  exact ⟨h77, WholeField.firstContactRestartLimStatement_of_lemmas Theorem15.aux25Statement h75 h77
    (Restart.firstContactWordKernelStatement_of_param h75 h77 h12p₀ h13₀ hFC)⟩

/-- **W5 on the canonical space**: the first clause of the sealed Theorem 1.5 (i) (`Theorem15.W5Statement` is exactly
its universal closure), at universe `0`. -/
theorem w5Statement_zero_closed : Theorem15.W5Statement.{0} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  exact (Seal.Final.IsFlowLine_stays_right_of_lt (hκ := hκ) (hκ4 := hκ4) (hb := hb) (hx := hx) (hθ := hθ)
    (hh := hh) (hη₁ := hη₁) (hη₂ := hη₂)).1

/-- **Lemma W0b on the canonical space, closed**: `Supp9.w0bStatement_of_lemma75` with Lemma 7.5 from Theorems 1.2–1.3. -/
theorem w0bStatement_zero_closed : Supp9.W0bStatement.{0} :=
  Supp9.w0bStatement_of_lemma75 (Restart.FCPlumb.lemma75Statement_of_thm12_thm13
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover Sec5.Aux61Cpt.theorem13Statement_of_cptCover)

/-- **No common open outgoing subarc at every first contact with two nonempty continuations, closed.** -/
theorem noCommonOutgoingArcStatement_closed : NoCommonOutgoingArcStatement.{u} :=
  noCommonOutgoingArcStatement_of_inputs lemma77_restartLim_closed.1 lemma77_restartLim_closed.2
    w5Statement_zero_closed w0bStatement_zero_closed

end Cross

/-! ### The strengthened Theorem 1.5 (iii) -/

/-- **Theorem 1.5 (iii), strengthened** (constant-angle interaction, crossing; paper p. 30: "if `θ₂ + π > θ₁ > θ₂`,
then `η^{x₁}_{θ₁}` may intersect `η^{x₂}_{θ₂}` and, upon intersecting, crosses and then never crosses back";
Proposition 7.12, p. 141; specification Theorem 7.12C, p. 542: "the first path crosses from the right of the second to
its left […] They have no common nontrivial open outgoing arc, and they cannot cross back"). With the hypotheses of the
frozen `IsFlowLine.crosses_of_lt` (`x₂ < x₁`, `θ₂ < θ₁ < θ₂ + π`): almost surely, if the flow lines have an interior
available contact, then their first contact `(s₀, t₀)` is attained at one common point, there the first curve crosses
the second from right to left in the stopped-order sense of the frozen `CrossesFromRightAt`, **and the outgoing
available paths `η₁([s₀, ζ₁))`, `η₂([t₀, ζ₂))` have no common open arc**: no open arc `η₁((a, a'))`,
`s₀ ≤ a < a' ≤ ζ₁`, lies in `η₂([t₀, ζ₂))`, and no open arc `η₂((c, c'))`, `t₀ ≤ c < c' ≤ ζ₂`, lies in
`η₁([s₀, ζ₁))`. If moreover `θ₁ - θ₂ ≥ πκ/(4 - κ)`, almost surely every interior available contact is the first
contact (the frozen critical-angle clause, unchanged). -/
def StrongCrossStatement : Prop :=
  ∀ {κ : ℝ} (_hκ : 0 < κ) (_hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (_hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (_hx : x₂ < x₁) (_hθ : θ₂ < θ₁) (_hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (_hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (_hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (_hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂),
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ ∧
          (∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ ω →
            ¬ η₁ ω '' Set.Ioo a a' ⊆ η₂ ω '' {t : ℝ≥0 | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂ ω}) ∧
          ∀ c c' : ℝ≥0, t₀ ≤ c → c < c' → (c' : ℝ≥0∞) ≤ ζ₂ ω →
            ¬ η₂ ω '' Set.Ioo c c' ⊆ η₁ ω '' {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) < ζ₁ ω}) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t)

/-- **The strengthened Theorem 1.5 (iii), proved**: the frozen crossing anchor (through its sealed provider) together
with the no-common-arc clause at the same first contact (`Cross.noCommonOutgoingArcStatement_closed` and Baire's
theorem, `Cross.noCommonOutgoingArc_of_prefix`, using the continuity of flow lines on their available intervals). -/
theorem strongCrossStatement_holds : StrongCrossStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨hcross, hcrit⟩ := Seal.Final.IsFlowLine_crosses_of_lt (hκ := hκ) (hκ4 := hκ4) (hb := hb)
    (hθ := hθ) (hθπ := hθπ) (hh := hh) (hη₁ := hη₁) (hη₂ := hη₂) (hx := hx)
  refine ⟨?_, hcrit⟩
  filter_upwards [hcross, Cross.noCommonOutgoingArcStatement_closed κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ
      P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, Sec7.ae_continuousOn_of_isFlowLine hη₁,
      Sec7.ae_continuousOn_of_isFlowLine hη₂] with ω hω hno hc₁ hc₂
  intro s t hst
  obtain ⟨s₀, t₀, h₀, hC⟩ := hω s t hst
  have hle := h₀.2.2.2 s t hst.1.le hst.2.1.le hst.2.2.1
  have hs₀ : (s₀ : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_le_coe.2 hle.1).trans_lt hst.1
  have ht₀ : (t₀ : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_le_coe.2 hle.2).trans_lt hst.2.1
  exact ⟨s₀, t₀, h₀, hC, Cross.noCommonOutgoingArc_of_prefix hc₁ hc₂ (hno s₀ t₀ h₀ hs₀ ht₀)⟩

/-- **The new statement strengthens the frozen one**: it implies `Wire.Crossing15Statement`, the exact universal type
of the frozen anchor `IsFlowLine.crosses_of_lt` (drop the two new conjuncts). -/
theorem crossing15Statement_of_strongCross (hS : StrongCrossStatement.{u}) : Wire.Crossing15Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨h1, h2⟩ := hS hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂
  refine ⟨?_, h2⟩
  filter_upwards [h1] with ω hω s t hst
  obtain ⟨s₀, t₀, h₀, hC, -⟩ := hω s t hst
  exact ⟨s₀, t₀, h₀, hC⟩

/-! ### What the new clause rules out, and its scope -/

/-- **Crossing excludes merging.** With the hypotheses of Theorem 1.5 (iii): almost surely, at the first contact of
every interior available contact, the first curve crosses the second (`CrossesFromRightAt`) and the two flow lines do
**not** agree as curves after it (`AgreeAsCurvesAfter`, the conclusion of the frozen merging clause (ii), fails). -/
theorem strongCross_not_agreeAsCurvesAfter {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
        CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ ∧
        ¬ AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀ := by
  filter_upwards [(strongCrossStatement_holds hκ hκ4 b jumps hb hx hθ hθπ hh hη₁ hη₂).1] with ω hω
  intro s t hst
  obtain ⟨s₀, t₀, h₀, hC, hA, -⟩ := hω s t hst
  have hle := h₀.2.2.2 s t hst.1.le hst.2.1.le hst.2.2.1
  exact ⟨s₀, t₀, h₀, hC, Cross.not_agreeAsCurvesAfter_of_noCommonOutgoingArc
    ((ENNReal.coe_le_coe.2 hle.1).trans_lt hst.1) ((ENNReal.coe_le_coe.2 hle.2).trans_lt hst.2.1) hA⟩

/-- **The new clause at every available contact** (real or interior; for combination with the contact-scope fix).
With the hypotheses of Theorem 1.5 (iii): almost surely, every contact `η₁ s = η₂ t` with `s < ζ₁`, `t < ζ₂` forces a
first contact `(s₀, t₀)` (Lemma 7.7) at which the outgoing available paths have no common open arc. -/
theorem noCommonOutgoingArc_upon_availableContact {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) < ζ₂ ω → η₁ ω s = η₂ ω t →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
        (∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ ω →
          ¬ η₁ ω '' Set.Ioo a a' ⊆ η₂ ω '' {t : ℝ≥0 | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂ ω}) ∧
        ∀ c c' : ℝ≥0, t₀ ≤ c → c < c' → (c' : ℝ≥0∞) ≤ ζ₂ ω →
          ¬ η₂ ω '' Set.Ioo c c' ⊆ η₁ ω '' {s : ℝ≥0 | s₀ ≤ s ∧ (s : ℝ≥0∞) < ζ₁ ω} := by
  filter_upwards [Cross.lemma77_restartLim_closed.1 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂
      hη₁ hη₂, Cross.noCommonOutgoingArcStatement_closed κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ
      P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, Sec7.ae_continuousOn_of_isFlowLine hη₁,
      Sec7.ae_continuousOn_of_isFlowLine hη₂] with ω h7 hno hc₁ hc₂
  intro s t hs ht hst
  obtain ⟨s₀, t₀, h₀, -, -⟩ := h7 ⟨s, t, hs.le, ht.le, hst⟩
  have hle := h₀.2.2.2 s t hs.le ht.le hst
  have hs₀ : (s₀ : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_le_coe.2 hle.1).trans_lt hs
  have ht₀ : (t₀ : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_le_coe.2 hle.2).trans_lt ht
  exact ⟨s₀, t₀, h₀, Cross.noCommonOutgoingArc_of_prefix hc₁ hc₂ (hno s₀ t₀ h₀ hs₀ ht₀)⟩

end AuditFix

end InteractingSLE
