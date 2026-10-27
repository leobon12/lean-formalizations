import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.Dtgt
import MatedCRTHarmonic.Frozen.OutDarts
import MatedCRTHarmonic.Frozen.Deg
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.Recurrent
import MatedCRTHarmonic.Frozen.VerticesMeeting
import MatedCRTHarmonic.Frozen.MatedCRTPath2
import MatedCRTHarmonic.Frozen.MatedCRTEdge
import MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import MatedCRTHarmonic.Frozen.MatedCRTGraph
import MatedCRTHarmonic.Frozen.MatedCRTField
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Statement definition: `LFMultigraph.IsHarmonicExtension`

One of the seven definitions of the statement surface of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here
called [18]. The definition is the frozen statement text, with the library namespace renamed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **[18] (1.6): `g` is the discrete harmonic function `f_ε` with boundary data `f`**, for a multigraph `G`
whose vertex `x` carries the cell `H x`. `f_ε` is a function on `V(D) = {x : H_x ∩ D ≠ ∅}` ([18] (1.5)); at a vertex
`x ∈ V(D)`:
* if `x ∈ V(∂D)` (`H_x ∩ ∂D ≠ ∅`), `g(x) = sup_{z ∈ H_x ∩ ∂D} f(z)` (stated as `IsLUB`, so no `sSup` junk value);
* otherwise `g` is discrete harmonic at `x`: `∑_{d leaves x} (g(x) − g(head d)) = 0`, i.e. `g(x)` is the average of
  `g` over the edge ends at `x` (loops twice, parallel edges with multiplicity).
Values of `g` off `V(D)` are unconstrained (`f_ε : V(D) → ℝ`). -/
def IsHarmonicExtension (H : V → Set ℂ) (D : Set ℂ) (f : ℂ → ℝ) (g : V → ℝ) : Prop :=
  ∀ x ∈ verticesMeeting H D,
    (x ∈ verticesMeeting H (frontier D) → IsLUB (f '' (H x ∩ frontier D)) (g x)) ∧
      (x ∉ verticesMeeting H (frontier D) → ∑ d ∈ G.outDarts x, (g x - g (G.dtgt d)) = 0)

end LFMultigraph

end MatedCRTHarmonic
