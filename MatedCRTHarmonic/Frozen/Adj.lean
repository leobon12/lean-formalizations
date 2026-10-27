import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph

/-!
# Frozen definition: `LFMultigraph.adj`

Adjacency `x ∼ y` (`x ≠ y` and some edge joins them) as a simple graph; graph paths and graph distance are those of
this simple graph (loops and multiplicities do not affect them).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- Adjacency `x ∼ y`: `x ≠ y` and some edge joins them. Graph paths and graph distance (`dist(·,·;G)`)
are those of this simple graph; loops and multiplicities do not affect them. -/
def adj : SimpleGraph V := SimpleGraph.fromRel fun x y => ∃ e, G.src e = x ∧ G.tgt e = y

end LFMultigraph

end MatedCRTHarmonic
