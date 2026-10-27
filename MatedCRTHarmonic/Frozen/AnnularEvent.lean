import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.Annulus
import MatedCRTHarmonic.Frozen.VerticesMeeting
import MatedCRTHarmonic.Frozen.Disconnects

/-!
# Frozen definition: `LFMultigraph.AnnularEvent`

One shared definition: finite exit time; the visited set `{X_m : m < τ}` disconnects; the cells up to
and including the exit lie in `A_{r/3,5r/3}(z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- The annular event of Definition 3.1(4) and Assumption 1.9(3) : the exit time `τ`
from `V_K(A_{r/2,3r/2}(z))` is finite, the visited set `{X_m : m < τ}` disconnects `V_K(∂B_{3r/4}(z))` from
`V_K(∂B_{5r/4}(z))`, and `⋃_{m ≤ τ} J_{X_m} ⊆ A_{r/3,5r/3}(z)`. -/
def AnnularEvent (J : V → Set ℂ) (z : ℂ) (r : ℝ) (X : ℕ → V) : Prop :=
  ∃ τ : ℕ, Markov.hitTime (verticesMeeting J (annulus z (r / 2) (3 * r / 2)))ᶜ X = τ ∧
    G.Disconnects {y | ∃ m < τ, X m = y}
      (verticesMeeting J (sphere z (3 * r / 4))) (verticesMeeting J (sphere z (5 * r / 4))) ∧
    ∀ m ≤ τ, J (X m) ⊆ annulus z (r / 3) (5 * r / 3)

end LFMultigraph

end MatedCRTHarmonic
