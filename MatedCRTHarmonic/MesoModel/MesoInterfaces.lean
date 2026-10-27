import Mathlib
import MatedCRTHarmonic.Frozen.IsCellCoupling
import MatedCRTHarmonic.Frozen.MesoscopicControlWith
import MatedCRTHarmonic.Frozen.ScaledGridControl
import MatedCRTHarmonic.CellFamily.Interfaces
import MatedCRTHarmonic.CellFamily.BadEventInterfaces
import MatedCRTHarmonic.CellFamily.WaypointStrongMarkovFixed
import MatedCRTHarmonic.CellFamily.ProducersCellCoupling
import MatedCRTHarmonic.CellFamily.ProducersGrid
import MatedCRTHarmonic.CellFamily.ProducersRouteM
import MatedCRTHarmonic.Frozen.CellModelExists
import MatedCRTHarmonic.MatedCRT.IsCorrelatedBM2Unique
import MatedCRTHarmonic.MesoModel.CloseTransfer

/-!
# Inputs for mesoscopic cell-model estimates

The probabilistic inputs are stated at the unit-cell coupling and dyadic-mesh level.
The event form of joint scaling below is the scale-transfer consequence of the equality in law of `(h_b, η^b)` with
`(h, η)` and the resulting cell-configuration identity.

The mesh families carry the **multigraph** identification
(`CellFamily.MultigraphCoupledRandomFamily`), the scaled-grid estimate inputs are bad-event (outer-measure)
bounds with no measurability fields, and the unit-mesh output is `UnitMesoscopicOutput`
(no Borel premise).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

/-- A cell-model sample space, together with its unit-mesh cell embedding and the mesh-indexed
embeddings used in the scaled-grid estimate. The sample space may be restricted to the full-measure event
on which all these geometric objects are defined. Its unit coupling is still the frozen
`IsCellCoupling` definition. The mesh family is a
`CellFamily.MultigraphCoupledRandomFamily`: almost surely each mesh graph *is* the mated-CRT multigraph
(`coupled.meshGraph_eq`), so its walk laws, degrees
and looplessness are those of `MatedCRT.graph`. -/
structure MatedCRTUnitMesoModel (γ : ℝ) where
  coupled : CellFamily.MultigraphCoupledRandomFamily γ
  standardBorel : StandardBorelSpace coupled.family.Ω
  unitLocallyFinite : ∀ ω, MatedCRT.IsLocallyFinite 1 (coupled.bm ω)
  unitEmbedding : ∀ ω,
    CellularEmbedding (MatedCRT.graph 1 (coupled.bm ω) (unitLocallyFinite ω)) 0
  unitEmbedding_cell : ∀ ω, (unitEmbedding ω).cell = coupled.cell ω
  radius : coupled.family.Ω → ℕ → ℝ
  radius_pos : ∀ ω k, 0 < radius ω k
  ρ : ℝ
  hρ : ρ ∈ Set.Ioo 0 1
  q : ℝ
  hq : 0 < q ∧ q < 2 / (2 + γ) ^ 2
  hγ : γ ∈ Set.Ioo 0 2

/-- The exponent `a_γ = 1/(γ(Q−γ)) = 1/(2−γ²/2)` in the cone-radius asymptotic. -/
def matedCRTUnitRadiusExponent (γ : ℝ) : ℝ := 1 / (2 - γ ^ 2 / 2)

/-- **Joint-scaling event-transfer interface.**
For every dyadic mesh and grid parameters, the failure probability of the scaled-grid
event on the mesh-`2⁻ᵏ` cell model equals the failure probability of its scaled version on the
unit-mesh embedding at radius `R_{2ᵏ}`. This follows from the joint quantum-cone / SLE
scaling law, with the deterministic Brownian graph rescaling in `MesoModel.TransferScaling`. This is
the event consequence consumed in the mesoscopic-control construction, rather than an extra estimate. -/
def MatedCRTProposition23GridScalingInput {γ : ℝ} (M : MatedCRTUnitMesoModel γ) : Prop :=
  ∀ k χ β p,
    M.coupled.family.P
      {ω | ¬ (M.unitEmbedding ω).ScaledGridControl (M.radius ω k)
        (CellFamily.mesh k) χ β M.q M.ρ p} =
    M.coupled.family.P
      {ω | ¬ (M.coupled.family.H k ω).ScaledGridControl 1
        (CellFamily.mesh k) χ β M.q M.ρ p}

/-- **Cone-radius asymptotic:** almost surely,
`log R_{2ᵏ}/(k log 2) → a_γ`. This base-2 logarithm form is algebraically equivalent to the
corresponding natural-log expression. This follows from the SLE-free radial Brownian last-passage / drift law of [17,
Lemma 2.6 and proof of Theorem 1.4], using the cone radial process. -/
def MatedCRTProposition24RadiusInput {γ : ℝ} (M : MatedCRTUnitMesoModel γ) : Prop :=
  ∀ᵐ ω ∂M.coupled.family.P,
    Tendsto (fun k : ℕ => Real.logb 2 (M.radius ω k) / (k : ℝ)) atTop
      (𝓝 (matedCRTUnitRadiusExponent γ))

/-- **Cell-count bound:** for every `δ > 0`, almost surely the number of unit-mesh
vertices meeting `B_{R_{2ᵏ}}(0)` is at most `2^((1+δ)k)` for all sufficiently large `k`. `ncard`
is paired with finiteness so that it represents the actual vertex count (the proof uses [16,
Lemma A.3], with `δ = 1` in the mesoscopic-control construction). Producer: the SLE-free whole-plane GMC moment
bound and the area identity for unit-mass cells, as detailed in the cell-counting argument. -/
def MatedCRTProposition25CellCountInput {γ : ℝ} (M : MatedCRTUnitMesoModel γ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop,
      let V := verticesMeeting (M.unitEmbedding ω).cell (ball (0 : ℂ) (M.radius ω k))
      V.Finite ∧ (V.encard.toNat : ℝ) ≤ 2 ^ ((1 + δ) * (k : ℝ))

/-- The probabilistic and geometric interfaces used to produce the scaled-grid estimate on the model's mesh
family. Every probability input is an outer-measure bound on a failure event, so no
measurability field is needed:
* `Lemma27CellDiamBad` — [18, Lemma 2.7] (producer: `lemma27_cells_transfer` from its
  GHM15/LQG small-cell inputs, packaged for the cone realization as
  `CellScaling.lemma27CellDiamBad_of_cone`);
* `Lemma38AnnulusHitBad` — the corrected uniform annulus-hitting estimate from [18, Lemma 3.8]
  (from the grid union bound over the one-scale estimate, with the
  per-scale Proposition 2.10 and Lemma 2.7 failure bounds);
* `WaypointStrongMarkovInputFixed2` — the corrected waypoint / iterated strong Markov input of
  the waypoint construction (positive `β₈, q`, the small-mesh restrictions, an
  environment net of `⌈4·10⁵/s₀²⌉` points; SLE-free);
* `PeanosphereG0` — bundle (Peanosphere fields) + G0BM (Brownian G0/`SideStrict`), which
  supplies Route M separation through `templateSeparation_of_peanosphereG0`.

Finite-grid count, graph connectivity and looplessness (the two graph premises of the waypoint
input) are produced, not assumed (`finiteGridCount_holds`, `graphConnected_ofCellCoupling`,
`MultigraphCoupledRandomFamily.ae_loopless`). -/
def MatedCRTCellFamilyInterfaces {γ : ℝ} (M : MatedCRTUnitMesoModel γ) : Prop :=
  CellFamily.Lemma27CellDiamBad M.coupled.family M.q M.ρ ∧
    CellFamily.Lemma38AnnulusHitBad M.coupled.family M.ρ ∧
    CellFamily.WaypointStrongMarkovInputFixed2 M.coupled.family M.q M.ρ ∧
    CellFamily.PeanosphereG0 M.coupled.family

end MatedCRTHarmonic.MesoModel
