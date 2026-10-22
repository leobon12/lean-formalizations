import HigherDimLQGMetric.Sec9.Closing
import HigherDimLQGMetric.Sec9.Claim32
import HigherDimLQGMetric.Sec9.OptUpper
import HigherDimLQGMetric.Sec9.MacroRatio
import HigherDimLQGMetric.Sec8b.Prop86

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.theorem14Sharp`

`theorem14Sharp_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/Theorem14Sharp.lean` verbatim ([S] Theorem 1.4 in the
sharp weak class). Proof: S8f's `theorem14Sharp_of_inputs` (the §9 closing argument, `Sec9/Closing.lean`) applied to S7b's
`prop86Stmt` (Prop 8.6, `Sec8b/Prop86.lean`), S8d's `optUpperShape` and `macroRatioShape` (optimal constants, (33)) and S8e's
`claim32_of` (claim (32)); rulings M34, M35. This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `theorem14Sharp`, proved. -/
theorem theorem14Sharp_impl :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsSharpWeakExpMetric d ξ Q D → IsSharpWeakExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) := by
  exact theorem14Sharp_of_inputs prop86Stmt optUpperShape (fun _ ξ Q hd => macroRatioShape hd ξ Q) claim32_of

end HigherDimLQGMetric
