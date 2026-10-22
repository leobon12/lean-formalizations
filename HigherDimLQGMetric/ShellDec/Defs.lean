import HigherDimLQGMetric.Core.Defs

/-!
# Gaussian shell decoupling: functional interface

The functional form of Appendix A, Lemma A.1, for events determined by mean-zero
pairings in geometrically shrinking annuli.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

/-- Functional form of shell decoupling for the mean-zero field sigma-algebras. -/
def ShellDecouplingFun0 (d : ℕ) : Prop :=
  ∀ a b q : ℝ, 0 < a → a < 1 → 1 < b → 0 < q → q < 1 →
  ∃ K : ℝ, 1 ≤ K ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ (z : Rd d) (r : ℕ → ℝ),
      (∀ i, 0 < r i) → (∀ i, r (i + 1) ≤ q * r i) →
      ∀ (I : Finset ℕ) (F : ℕ → Ω → ℝ),
        (∀ i, ∃ G : Ω → ℝ, Measurable[fieldSigma0 h (ann z (a * r i) (b * r i))] G ∧
          F i =ᵐ[P] G) →
        (∀ i ω, 0 ≤ F i ω ∧ F i ω ≤ 1) →
        ∫ ω, ∏ i ∈ I, F i ω ∂P ≤ ∏ i ∈ I, (∫ ω, F i ω ^ K ∂P) ^ K⁻¹

end HigherDimLQGMetric
