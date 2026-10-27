import MatedCRTHarmonic.GoodScales.Times
import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Adj
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.WalkLaw

/-!
# Good scales: the strong Markov induction

The strong Markov induction of the strong Markov induction, conditioned version. Writing `E` for the paths from
`x` that first enter `A` at `v` (and are admissible), `F_j = reach j ∩ D_j` (first success at scale
`j`) and `Φ_j = P(E ∪ ⋃_{j ≤ i < K} F_i)`:

* `Φ_j = P(F_j) + Φ_{j+1}` (disjoint union: a success excludes a first entry at `v`, and `F_i`
  lies in the failure set of every earlier scale);
* `Φ_j ≤ P(reach j)` (`E` and the later `F_i` reach scale `j`);
* `p · P(reach j) ≤ P(F_j)` (strong Markov property at `sig j` on `{sig j < ⊤}`, no finiteness);

hence `Φ_{j+1} ≤ (1 - p) Φ_j`, so `P(E) = Φ_K ≤ (1 - p)^K Φ_0 ≤ (1 - p)^K P(τ_A < ⊤)`
for the walk events used here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GoodScales

open Markov

variable {V E : Type*}

section Events

variable (G : LFMultigraph V E)

/-- The admissible paths from `x`: they start at `x` and move along edges. -/
def goodPath (x : V) : Set (ℕ → G.State) :=
  {ω | ω 0 = Sum.inl x ∧ ∀ n, StepOK G (G.vertexPath ω n) (G.vertexPath ω (n + 1))}

/-- First entry into `A` at the vertex `v`. -/
def entryAt (A : Set V) (v : V) : Set (ℕ → G.State) :=
  {ω | hitTime (vset G A) ω < ⊤ ∧ G.stateVertex (stopState (hitTime (vset G A)) ω) = v}

end Events

variable {G : LFMultigraph V E} {J : V → Set ℂ} {z : ℂ} {r : ℕ → ℝ}
  {A : Finset V} {v : V} {K : ℕ} {p : ℝ}

/-- The admissible paths carry the whole law of the walk. -/
theorem walkLaw_compl_goodPath [Countable G.State] (x : V) :
    G.walkLaw x (goodPath G x)ᶜ = 0 :=
  ae_iff.mp (ae_start_and_stepOK G (Sum.inl x))

/-! ### From the entry vertex to the entry edge -/

-- The frozen statement carries `hconn`, `hv` and `hx`; the bound holds without them (if `A` is never
-- hit, `harm^x_A = 0`; a walk started in `A` has no entry edge).

end MatedCRTHarmonic.GoodScales
