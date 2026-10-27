import Mathlib
import MatedCRTHarmonic.Frozen.CellModelExists
import MatedCRTHarmonic.Frozen.Recurrent
import MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2Unique
import MatedCRTHarmonic.MatedCRT.LocalFiniteness
import MatedCRTHarmonic.MesoModel.AssemblyInterfaces
import MatedCRTHarmonic.Frozen.Adj
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.IsConnectedSet
import MatedCRTHarmonic.HarmonicInfinity.Mesoscopic
import MatedCRTHarmonic.Implementation.MatedCRTGraphConnected
import MatedCRTHarmonic.Frozen.CellularEmbedding
import MatedCRTHarmonic.Frozen.MesoscopicControlWith
import MatedCRTHarmonic.Harmonic.Harm
import MatedCRTHarmonic.Harmonic.Graph
import MatedCRTHarmonic.Growth.ChainRates
import MatedCRTHarmonic.Markov.Chain
import MatedCRTHarmonic.GoodScales.Bound
import MatedCRTHarmonic.CellularFacts.Basic
import MatedCRTHarmonic.Frozen.AnnularEvent
import MatedCRTHarmonic.Frozen.VerticesMeeting
import MatedCRTHarmonic.MesoModel.TransferScaling
import MatedCRTHarmonic.MesoModel.CloseTransfer

/-!
# Consequences of `CellModelExists` for every mesh and correlated law

`CellModelExists γ` supplies one standard-Borel cell coupling on which, almost surely, the unit-mesh
graph of `bm ω` is locally finite, recurrent and has a cellular embedding with mesoscopic control at
fixed constants `p, σ, ν`. This module derives from it three inputs valid for every mesh and every
correlated law:

* local finiteness: MG's `ae_isLocallyFinite_holds` (no coupling needed);
* recurrence (the recurrence result) and mesoscopic control (the mesoscopic-control construction): the unit-mesh events are moved
  from the coupling to every correlated law by `closeAe_map_path2_of_ae_comp` (disintegration on the
  standard Borel `Ω`, no measurability of the events) and the uniqueness of the law
  (`isCorrelatedBM2_unique_holds`), then to mesh `ε` by Brownian rescaling
  `unitRescalePath` and its graph identification `graphCast_eq_unitRescalePath`.

-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u v

namespace MatedCRTHarmonic.MesoModel

/-- **A.e. transfer from a cell coupling to any correlated law, for an arbitrary path event.**
Uniqueness identifies `P.map bm` with `μ`; the standard-Borel disintegration transfer removes the
need for the event to be Borel. -/
theorem closeAe_of_cellCoupling
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {γ : ℝ} {P : Measure Ω} {bm : Ω → MatedCRT.Path2} {cell : Ω → ℤ → Set ℂ}
    (hc : MatedCRT.IsCellCoupling γ P bm cell)
    {μ : Measure MatedCRT.Path2} (hμ : MatedCRT.IsCorrelatedBM2 γ μ)
    {Q : MatedCRT.Path2 → Prop} (hQ : ∀ᵐ ω ∂P, Q (bm ω)) : ∀ᵐ x ∂μ, Q x := by
  have : IsProbabilityMeasure (P.map bm) := hc.law.isProbabilityMeasure
  have : IsProbabilityMeasure P :=
    Measure.isProbabilityMeasure_of_map hc.measurable_bm.aemeasurable
  have hEq : P.map bm = μ :=
    MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ (P.map bm) μ hc.law hμ
  rw [← hEq]
  exact closeAe_map_path2_of_ae_comp hc.measurable_bm hQ

/-- **Mesh change.** A unit-mesh event holding a.s. on a cell coupling holds a.s. for the
`ε`-rescaled path under every correlated law: the rescaled law is again correlated
(`isCorrelatedBM2_map_unitRescalePath`), and pulling an a.e. statement back along a measurable map
needs no measurability of the event. -/
theorem closeAe_unitRescalePath_of_cellCoupling
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {γ : ℝ} {P : Measure Ω} {bm : Ω → MatedCRT.Path2} {cell : Ω → ℤ → Set ℂ}
    (hc : MatedCRT.IsCellCoupling γ P bm cell)
    {ε : ℝ} (hε : 0 < ε) {μ : Measure MatedCRT.Path2} (hμ : MatedCRT.IsCorrelatedBM2 γ μ)
    {Q : MatedCRT.Path2 → Prop} (hQ : ∀ᵐ ω ∂P, Q (bm ω)) :
    ∀ᵐ ω ∂μ, Q (unitRescalePath ε ω) := by
  have hscale : MatedCRT.IsCorrelatedBM2 γ (μ.map (unitRescalePath ε)) :=
    isCorrelatedBM2_map_unitRescalePath hε hμ
  exact ae_of_ae_map (measurable_unitRescalePath ε).aemeasurable
    (closeAe_of_cellCoupling hc hscale hQ)

/-- Recurrence is transported along the edge-type identification of two graphs. -/
private theorem closeRecurrent_of_castGraph {V : Type v} {E F : Type u} (hEF : E = F)
    {G : LFMultigraph V E} {G' : LFMultigraph V F}
    (hG : cast (congrArg (LFMultigraph V) hEF) G = G') (hrec : G'.Recurrent) :
    G.Recurrent := by
  cases hEF
  change G = G' at hG
  subst G'
  exact hrec

/-- The recurrence of the unit-mesh graph of the rescaled path gives the recurrence of the mesh-`ε`
graph of the original path. -/
theorem closeRecurrent_of_unitRescalePath {ε : ℝ} (hε : 0 < ε)
    (ω : MatedCRT.Path2) (hεlf : MatedCRT.IsLocallyFinite ε ω)
    (h1lf : MatedCRT.IsLocallyFinite 1 (unitRescalePath ε ω))
    (hrec : (MatedCRT.graph 1 (unitRescalePath ε ω) h1lf).Recurrent) :
    (MatedCRT.graph ε ω hεlf).Recurrent :=
  closeRecurrent_of_castGraph (edgeTypeEq_unitRescalePath hε ω)
    (graphCast_eq_unitRescalePath hε ω hεlf h1lf) hrec

/-- **the recurrence result for every mesh and law, from `CellModelExists`.** The coupling's unit-mesh
recurrence is transferred to every correlated law and rescaled to mesh `ε`. -/
theorem matedCRTRecurrenceInput_of_cellModel {γ : ℝ} (hmodel : MatedCRT.CellModelExists γ) :
    MatedCRTRecurrenceInput γ := by
  rcases hmodel with ⟨Ω, mΩ, hstd, P, bm, cell, p, σ, ν, hc, hgood⟩
  intro ε hε μ hμ
  have hunit : ∀ᵐ ω ∂P, ∃ h : MatedCRT.IsLocallyFinite 1 (bm ω),
      (MatedCRT.graph 1 (bm ω) h).Recurrent := by
    filter_upwards [hgood] with ω hω
    obtain ⟨h, hrec, _⟩ := hω
    exact ⟨h, hrec⟩
  filter_upwards [closeAe_unitRescalePath_of_cellCoupling hc hε hμ
    (Q := fun x => ∃ h : MatedCRT.IsLocallyFinite 1 x, (MatedCRT.graph 1 x h).Recurrent) hunit]
    with ω hω hεlf
  obtain ⟨h1lf, hrec⟩ := hω
  exact closeRecurrent_of_unitRescalePath hε ω hεlf h1lf hrec

end MatedCRTHarmonic.MesoModel
