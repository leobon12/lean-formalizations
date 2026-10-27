import MatedCRTHarmonic.Frozen.CellModelExists
import MatedCRTHarmonic.MesoModel.AssemblyInterfaces
import MatedCRTHarmonic.MesoModel.CloseCellModel
import MatedCRTHarmonic.MesoModel.MesoInterfaces

/-!
# Cell-model existence

This module factors the final assembly of the frozen `CellModelExists` statement through the
unit-mesh mesoscopic estimate and the recurrence result for all meshes and correlated laws. The model data are
the common standard-Borel SLE/cell coupling, with the cell-valued embedding already tied to that
coupling. The probabilistic and SLE inputs are recorded in `MesoInterfaces`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

/-- **Mesoscopic output on a fixed mating-of-trees cell model.** The constants are deterministic for the
given `γ`, and the very same embedding whose cells are identified with the coupled SLE cells
satisfies mesoscopic control almost surely. This follows from the scaling, cell-count, annular, and mesoscopic-control estimates, with
the named inputs in `MesoInterfaces`. -/
def UnitMesoscopicOutput {γ : ℝ} (M : MatedCRTUnitMesoModel γ) : Prop :=
  ∃ p σ ν : ℝ, ∀ᵐ ω ∂M.coupled.family.P,
    (M.unitEmbedding ω).MesoscopicControlWith p σ ν

/-- The cell-model existence statement follows from the unit-mesh mesoscopic estimate and
the recurrence interface. Recurrence is transferred to the model's own path law; the
`unitEmbedding_cell` field preserves the exact cell identity required by frozen
`MatedCRT.CellModelExists`. -/
theorem cellModelExists_of_inputs {γ : ℝ} (M : MatedCRTUnitMesoModel γ)
    (hmeso : UnitMesoscopicOutput M) (hrec : MatedCRTRecurrenceInput γ) :
    MatedCRT.CellModelExists γ := by
  rcases hmeso with ⟨p, σ, ν, hmeso⟩
  let D := M.coupled
  let μ : Measure MatedCRT.Path2 := D.family.P.map D.bm
  have hrecμ : ∀ᵐ x ∂μ, ∀ h : MatedCRT.IsLocallyFinite 1 x,
      (MatedCRT.graph 1 x h).Recurrent := hrec 1 one_pos μ D.coupling.law
  have hrecP : ∀ᵐ ω ∂D.family.P, ∀ h : MatedCRT.IsLocallyFinite 1 (D.bm ω),
      (MatedCRT.graph 1 (D.bm ω) h).Recurrent :=
    ae_of_ae_map D.coupling.measurable_bm.aemeasurable hrecμ
  refine ⟨D.family.Ω, D.family.mΩ, M.standardBorel, D.family.P, D.bm, D.cell,
    p, σ, ν, D.coupling, ?_⟩
  filter_upwards [hmeso, hrecP] with ω hmesoω hrecω
  exact ⟨M.unitLocallyFinite ω, hrecω (M.unitLocallyFinite ω),
    M.unitEmbedding ω, M.unitEmbedding_cell ω, hmesoω⟩

end MatedCRTHarmonic.MesoModel
