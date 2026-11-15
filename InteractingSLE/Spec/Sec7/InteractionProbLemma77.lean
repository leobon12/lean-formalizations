import InteractingSLE.Spec.Sec7.InteractionProbFirstContact
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Lemma 7.7's common first contact for flow lines, from Aux. lemmas 70, 72 and 25

Packet PROVE-SEC7-B2 (Specification §7.2, Lemma 7.7, p. 282).

The first-contact input of the Theorem 1.5 assembly, `Theorem15.W8FirstContactStatement` (Theorem W8 at `σ = 0`,
pp. 538–539), is also the common-first-point assertion of Lemma 7.7 with `Tᵢ = ζᵢ` ("if `τᵢ ≤ Tᵢ` and `τᵢ < ∞` for
`i = 1, 2` then `η₁(τ₁) = η₂(τ₂)`"). Here it is derived by Lemma 7.7's own proof (`InteractionProbFirstContact.lean`)
from three statements:

* `Theorem15.Aux25Statement` (Aux. lemma 25, §4.2, p. 127: simplicity);
* `Aux70Statement` (Aux. lemma 70, §7.2, p. 274) and `Aux72Statement` (Aux. lemma 72, §7.2, p. 278): §7.2
  statements that are **not proved in Lean** (see the handoff for their missing inputs).

So `w8FirstContactStatement_of_aux70_of_aux72` is a conditional helper, recorded as the exact remaining obligation
of §7.2's route to the first-contact input. The assembly in `Theorem15.lean` does not use it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-- **Aux. lemma 70** (exclusion of a reverse minimal common arc, p. 274), for the flow lines of Lemma 7.7 stopped at
their available lifetimes `Tᵢ = ζᵢ`, at every integer truncation `ζᵢ ∧ m` (Lemma 7.7's proof, p. 282): "Assume the
single-path, history-marked GFF couplings and field determination used in Lemma 7.7, with `0 < κ < 4` and
`θ₁ < θ₂ + π`. Almost surely, the first-coordinate projection of the set of minimal contacts from Aux. lemma 68
contains no nondegenerate interval." A §7.2 statement **not proved in Lean**. -/
def Aux70Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ m : ℕ, ∀ᵐ ω ∂P,
        NoReverseMinimalArc (η₁ ω) (truncTime (ζ₁ ω) m) (η₂ ω) (truncTime (ζ₂ ω) m)

/-- **Aux. lemma 72** (a countable adapted witness for every minimal lens, p. 278), for the flow lines of Lemma 7.7
stopped at their available lifetimes, at every integer truncation `ζᵢ ∧ m`: "In the coupled setup of Lemma 7.7,
assume the finite-prefix first-exit assertion of Lemma 7.6 […]. Then almost surely there are no two adjacent
minimal contacts with distinct points." A §7.2 statement **not proved in Lean**. -/
def Aux72Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ m : ℕ, ∀ᵐ ω ∂P,
        NoAdjacentMinimalContacts (η₁ ω) (truncTime (ζ₁ ω) m) (η₂ ω) (truncTime (ζ₂ ω) m)

/-- A flow line is almost surely continuous on its available interval `{t | t ≤ ζ}` (its translate is a continuous
generating trace, `IsFlowLine`). -/
theorem ae_continuousOn_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
  obtain ⟨_, _, W, _, _, _, -, -, htr⟩ := hη
  filter_upwards [htr] with ω hω
  have hc : ContinuousOn (fun t => (η ω t - x) + x) {t | (t : ℝ≥0∞) ≤ ζ ω} :=
    hω.2.1.add continuousOn_const
  simpa only [sub_add_cancel] using hc

/-- **Lemma 7.7's common first contact for flow lines** (p. 282), and hence the first-contact input of the
Theorem 1.5 assembly, from Aux. lemmas 25, 70 and 72 (a conditional helper: Aux. 70 and 72 are not proved). -/
theorem w8FirstContactStatement_of_aux70_of_aux72 (h25 : Theorem15.Aux25Statement.{u})
    (h70 : Aux70Statement.{u}) (h72 : Aux72Statement.{u}) : Theorem15.W8FirstContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  exact ae_exists_isFirstContact_of_truncations (ae_continuousOn_of_isFlowLine hη₁)
    (ae_continuousOn_of_isFlowLine hη₂) (Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₁)
    (Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₂)
    (h70 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂)
    (h72 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂)

end Sec7

end InteractingSLE
