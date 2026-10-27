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
# Statement definition: `dirichletEnergy`

One of the seven definitions of the statement surface of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here
called [18]. The definition is the frozen statement text, with the library namespace renamed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

/-- **[18] Definition 1.2 for differentiable functions**: `Energy(f; D) = ∫_D |∇f(z)|² dz`. Defined only for an
open `D` (argument `_hD`) and `f` differentiable on `D` (argument `_hf`); on an open `D` this makes `f` differentiable
at every point of `D`, so `fderiv ℝ f z` is the pointwise gradient there and never `fderiv`'s junk value.
`‖fderiv ℝ f z‖` is the operator norm of `df_z : ℂ →L[ℝ] ℝ`, which equals the Euclidean norm `|∇f(z)|`. -/
def dirichletEnergy (f : ℂ → ℝ) (D : Set ℂ) (_hD : IsOpen D) (_hf : DifferentiableOn ℝ f D) : ℝ≥0∞ :=
  ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)

end MatedCRTHarmonic
