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
import MatedCRTHarmonic.Frozen.IsHarmonicExtension

/-!
# Statement definition: `LFMultigraph.IsTutteEmbedding`

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

/-- **The Tutte embedding with identity boundary data** ([18] §1.6): `Φ = Φ₁ + iΦ₂ : V → ℂ ≅ ℝ²`, where `Φ₁`
(resp. `Φ₂`) is the function `f_ε` of (1.6) for `f(z) = Re z` (resp. `f(z) = Im z`). `ℂ` carries the Euclidean norm,
so `‖Φ x − Φ y‖` is the Euclidean length `|Φ^ε(x) − Φ^ε(y)|` of (1.10). -/
def IsTutteEmbedding (H : V → Set ℂ) (D : Set ℂ) (Φ : V → ℂ) : Prop :=
  G.IsHarmonicExtension H D (fun z => z.re) (fun x => (Φ x).re) ∧
    G.IsHarmonicExtension H D (fun z => z.im) (fun x => (Φ x).im)

end LFMultigraph

end MatedCRTHarmonic
