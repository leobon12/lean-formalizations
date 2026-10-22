import HigherDimLQGMetric.Assembly.Theorem14Sharp
import HigherDimLQGMetric.Main.WeakUniqueness
import HigherDimLQGMetric.Thm16.Theorem16
import HigherDimLQGMetric.Sec4.Prop42
import HigherDimLQGMetric.LfppTight.TightMain
import HigherDimLQGMetric.DGZ.ExportRealEps

/-!
# Provider of the frozen theorem `HigherDimLQGMetric.theorem14`

`theorem14_impl` states the frozen anchor `HigherDimLQGMetric/Frozen/Theorem14.lean` verbatim ([S] Theorem 1.4, uniqueness in the
weak class). Proof: L10a's `theorem14_of_inputs` (`Main/WeakUniqueness.lean`: every weak assignment is sharp weak at
`distExp d ξ` by [1] Theorem 1.6, then uniqueness in the sharp weak class) with L9c's `theorem16Shape_of` ([1] Theorem 1.6, made
unconditional by L9b's `prop42Shape_of`, L6a's `l6a_tight'` and L5b's `realEpsAdapterShape`) and `theorem14Sharp_impl`. This
module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The frozen statement of `theorem14`, proved. -/
theorem theorem14_impl :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ (D D' : DistRd d → ContMetric d) (c c' : ℝ → ℝ),
      IsWeakExpMetric d ξ D c → IsWeakExpMetric d ξ D' c' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) := by
  exact theorem14_of_inputs (theorem16Shape_of (prop42Shape_of l6a_tight' DGZ.realEpsAdapterShape) DGZ.realEpsAdapterShape l6a_tight') theorem14Sharp_impl

end HigherDimLQGMetric
