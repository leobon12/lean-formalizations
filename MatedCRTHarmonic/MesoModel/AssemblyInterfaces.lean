import Mathlib
import MatedCRTHarmonic.Frozen.CellModelExists
import MatedCRTHarmonic.Frozen.CellularEmbedding
import MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import MatedCRTHarmonic.Frozen.MatedCRTGraph
import MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import MatedCRTHarmonic.Frozen.MesoscopicControlWith

/-!
# Interfaces for cell-model assembly

These inputs support the cell-model and random-walk estimates.
Local finiteness is separated from recurrence because it supplies the graph constructor's witness.
The recurrence interface is the recurrence result, and the uniform mesoscopic interface is
`MesoscopicControlWith` as supplied by the scaling, cell-count, annular, and mesoscopic-control estimates. The cell-model identification interface is
`MatedCRT.CellModelExists`: its `IsCellCoupling` witness identifies the cellular embedding with
the Brownian-defined mated-CRT graph.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

/-- **the recurrence result input** for the cell-model construction (paper; producer: G3's recurrence
work from [18, Theorem 1.4], with the Prop. 2.10/Lemma 2.7 inputs recorded in the proof). For every
positive mesh and the law of [18] §1.1, simple random walk on the locally finite graph is
almost surely recurrent. -/
def MatedCRTRecurrenceInput (γ : ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ (μ : Measure MatedCRT.Path2), MatedCRT.IsCorrelatedBM2 γ μ →
    ∀ᵐ ω ∂μ, ∀ h : MatedCRT.IsLocallyFinite ε ω,
      (MatedCRT.graph ε ω h).Recurrent

end MatedCRTHarmonic.MesoModel
