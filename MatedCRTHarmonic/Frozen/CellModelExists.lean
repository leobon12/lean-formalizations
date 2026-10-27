import Mathlib
import MatedCRTHarmonic.Frozen.CellularEmbedding
import MatedCRTHarmonic.Frozen.MesoscopicControlWith
import MatedCRTHarmonic.Frozen.Recurrent
import MatedCRTHarmonic.Frozen.MatedCRTPath2
import MatedCRTHarmonic.Frozen.MatedCRTEdge
import MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import MatedCRTHarmonic.Frozen.MatedCRTGraph
import MatedCRTHarmonic.Frozen.IsCellCoupling

/-!
# Frozen definition: `MatedCRT.CellModelExists`

Interface (standard Borel); discharged by `exists_cellModel`; used as an input to a conditional cell-model theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

namespace MatedCRT

/-- **Existence of a recurrent mated-CRT cellular model with mesoscopic control** (a proposition discharged by `exists_cellModel`): there is a cell coupling on a
standard Borel probability space whose unit-mesh map is almost surely recurrent and whose cells
almost surely satisfy `MesoscopicControlWith` with deterministic constants `p, σ, ν`. -/
def CellModelExists (γ : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω) (bm : Ω → Path2)
    (cell : Ω → ℤ → Set ℂ) (p σ ν : ℝ),
    IsCellCoupling γ P bm cell ∧
      ∀ᵐ ω ∂P, ∃ h : IsLocallyFinite 1 (bm ω), (graph 1 (bm ω) h).Recurrent ∧
        ∃ H : CellularEmbedding (graph 1 (bm ω) h) 0, H.cell = cell ω ∧ H.MesoscopicControlWith p σ ν

end MatedCRT

end MatedCRTHarmonic
