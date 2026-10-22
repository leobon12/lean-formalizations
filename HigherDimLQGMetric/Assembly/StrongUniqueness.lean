import HigherDimLQGMetric.Assembly.Theorem14Sharp
import HigherDimLQGMetric.Sec10.StrongUniq

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.strongUniqueness`

`strongUniqueness_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/StrongUniqueness.lean` verbatim (uniqueness of
strong assignments). Proof: S8c's `strongUniqueness_of` (`Sec10/StrongUniq.lean`: strong ⇒ sharp weak by S8a's `lemma101`, then
uniqueness in the sharp weak class) applied to `theorem14Sharp_impl` (provider `Assembly/Theorem14Sharp.lean`). This module
imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `strongUniqueness`, proved. -/
theorem strongUniqueness_impl :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ Q D → IsStrongExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) := by
  exact strongUniqueness_of theorem14Sharp_impl

end HigherDimLQGMetric
