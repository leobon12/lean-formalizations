/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Datum

/-!
# Lemma 7.5 in data-measurable form

Packet PROVE-RESTART-CPL, step (1). The landed named input `Theorem15.Lemma75Statement` gives, for each boundary datum,
one Borel map `Φ_b` of the field. A choice of `Φ_b` for each `b` need not be measurable in `b`
(`planning/handoffs/PROVE-SUPP10-B.md`, "Pitfall"), and the first-contact restart applies determination to a field
whose datum is random. The specification states the data-measurable form (supplement §2.6, p. 456: "Disintegrate jointly
over the initial datum and field on their standard Borel spaces; a common Borel graph then determines the next piece";
Lemma 7.5's proof, p. 252: "The finitely many possible amalgamated seed-weight pairs and countably many chosen radii
supply a measurable restart rule").

* `Lemma75DataStatement`: one map `Φ : BoundaryWord × field → ℝ≥0∞ × path`, **jointly measurable**, giving the
  lifetime and the available path of every flow line of every field whose datum is the word `c`.
* `lemma75Statement_of_lemma75DataStatement`: it implies the landed per-datum `Lemma75Statement` (through the
  representation of every piecewise-constant datum by a word, `BoundaryWord.exists_fn_eq`).

The restart itself does not need this statement: in the conditional-kernel form of the restart carrier
(`Restart/Carrier.lean`) the per-datum statement is applied to the conditional law at each datum and only measurable
events are integrated (`Restart/Integrate.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

/-- **Lemma 7.5, data-measurable form** (p. 252; supplement §2.6, p. 456): for `0 < κ < 4`, every seed `x` and angle
`θ` there is one jointly Borel map `Φ` of the boundary word and the field giving the lifetime and the
capacity-parametrized available path of every angle-`θ` flow line from `x` of every field whose boundary datum is the
word. -/
def Lemma75DataStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ x θ : ℝ,
    ∃ Φ : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
    ∀ (c : BoundaryWord) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h c.fn c.jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ c.fn c.jumps x θ P h η ζ →
      ∀ᵐ ω ∂P, (Φ (c, h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → (Φ (c, h ω)).2 t = η ω t

/-- **The data-measurable form implies the per-datum form** `Theorem15.Lemma75Statement`: represent the datum by a
word and freeze the word coordinate of `Φ`. -/
theorem lemma75Statement_of_lemma75DataStatement (H : Lemma75DataStatement.{u}) :
    Theorem15.Lemma75Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ
  obtain ⟨c, hcJ, hcb⟩ := BoundaryWord.exists_fn_eq hb
  obtain ⟨Φ, hΦm, hΦ⟩ := H κ hκ hκ4 x θ
  refine ⟨fun g => Φ (c, g), hΦm.comp (measurable_const.prodMk measurable_id), ?_⟩
  intro Ω _ P _ h hh η ζ hη
  exact hΦ c P h ((BoundaryWord.isGFFWithBoundaryData_fn_iff hcJ hcb P h).2 hh) η ζ
    ((BoundaryWord.isFlowLine_fn_iff hcJ hcb).2 hη)

end Restart

end InteractingSLE
