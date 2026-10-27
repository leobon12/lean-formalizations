import Mathlib
import LQGMetric.Statement.GFF
import MatedCRTHarmonic.MesoModel.MesoInterfaces
import MatedCRTHarmonic.CellScaling.ConeDefs

/-!
# The SLE/LQG cone realization of the unit-mesh model, and the named inputs of the scaling and cell-count estimates

`MesoModel.MatedCRTUnitMesoModel γ` is an abstract unit-mesh model whose
`radius ω k` is an arbitrary positive number. the scaling and cell-count estimates concern the **SLE/LQG cell model**:
the field is the circle-average embedding `h` of a γ-quantum cone, `η` is an independent whole-plane
space-filling SLE parameterized by `A^γ_h`-area, the cells are `H^ε_x = η([ε(x−1), εx])`, and `R_{2^k}` is the cone
scale of that cone. `ConeRealization M` records that `M` *is* this model: it carries the cone data (whole-plane GFF `X`,
radial Brownian motions `B, B'`, curve `η`) with their defining laws, and the identifications of `M`'s radius and cells
(the mesh multigraphs are identified by the model family's own `M.coupled.meshGraph_eq`).
This also identifies the data needed for Lemma 2.7 with the coupling `MatingOfTreesInput`.

The named inputs have the following sources:
* **Coupling fields (SLE-dependent):** `BoundaryLengthCovariance` (field `boundaryLength`),
  `AreaParametrization` (bundle field `areaParam`, with `η(0) = 0`).
* **Composite:** `Prop23JointScaling` (the joint-scaling identity as printed), from the SLE-free
  [14, Prop 4.13(i)], random-dilation area covariance, and the coupling fields
  `igMap`, `indep_curve`, and `areaParam`.
* **SLE-free, to prove:** `AreaScalingLaw` ([14, Prop 4.13(i)] + [SW, Thm 1.4]; CS1 + LR1), `AreaBallMoment`
  ([16, Lemma A.3]), `MeshGridEventMeasurable` (measurability of the scaled-grid estimate event as a function of the data).
* **Produced downstream (the mesoscopic argument):** `UnitCellDiamEventually` (clause (1) of the a.s. eventual unit-scale
  the scaled-grid estimate event, which `MesoModel.matedCRTUnitMesoscopicInput_of_interfaces` derives as `hEventuallyScaled`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- **The SLE/LQG cone realization of a unit-mesh model.** On the sample space of `M`:
* `X` is a whole-plane GFF and `B, B'` are standard Brownian motions, with `X ⊥ (B, B')` and `B ⊥ B'`: this is the
  definition of the circle-average embedding `h = coneFieldOf γ X B B'` of the γ-quantum cone (DMS
  Def 4.10, Rem 4.4);
* `curve` is the space-filling SLE `η` parameterized by `A^γ_h`-area, measurable;
* `M.radius ω k = R_{2^k}`, `M`'s unit cells are `η([x − 1, x])`, and the mesh-`2^{-k}`
  cells of `M`'s random family are `η([2^{-k}(x − 1), 2^{-k}x])`, almost surely.

The identification of the mesh-`2^{-k}` graphs of the family with the mated-CRT multigraphs `G^{2^{-k}}` of
`M.coupled.bm` (Definition 1.12; multiplicities matter for the walk) was this
structure's field `meshGraph_eq`; since it is carried by the model's family itself,
`M.coupled.meshGraph_eq` (`CellFamily.MultigraphCoupledRandomFamily`). -/
structure ConeRealization {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ) where
  /-- The whole-plane GFF whose lateral part is the lateral part of the cone field. -/
  X : M.coupled.family.Ω → LQGMetric.DistC
  /-- The radial Brownian motion for `r ≤ 1` (`A_t = B_t + γt`, `t ≥ 0`). -/
  B : ℝ≥0 → M.coupled.family.Ω → ℝ
  /-- The radial Brownian motion for `r ≥ 1` (conditioned through its last zero, DMS Rem 4.4). -/
  B' : ℝ≥0 → M.coupled.family.Ω → ℝ
  /-- The space-filling SLE `η`, parameterized by LQG area with `η(0) = 0`. -/
  curve : M.coupled.family.Ω → C(ℝ, ℂ)
  gff : LQGMetric.IsWholePlaneGFF X M.coupled.family.P
  brownian : IsBrownianReal B M.coupled.family.P
  brownian' : IsBrownianReal B' M.coupled.family.P
  indep : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) M.coupled.family.P ∧
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) M.coupled.family.P
  measurable_curve : Measurable curve
  radius_eq : ∀ᵐ ω ∂M.coupled.family.P, ∀ k : ℕ,
    M.radius ω k = coneScale γ γ (fun t => B t ω) (fun t => B' t ω) ((2 : ℝ) ^ k)
  cell_eq : ∀ᵐ ω ∂M.coupled.family.P, ∀ x : ℤ, M.coupled.cell ω x = curve ω '' Icc ((x : ℝ) - 1) x
  meshCell_eq : ∀ k : ℕ, ∀ᵐ ω ∂M.coupled.family.P, ∀ x : ℤ,
    (M.coupled.family.H k ω).cell x = meshCells (CellFamily.mesh k) (curve ω) x

namespace ConeRealization

variable {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M)

/-- The γ-quantum cone field `h` (circle-average embedding) of the realization. -/
def field (ω : M.coupled.family.Ω) : LQGMetric.DistC :=
  coneFieldOf γ (D.X ω) (fun t => D.B t ω) (fun t => D.B' t ω)

/-- The cone scale `R_b`. -/
def scale (b : ℝ) (ω : M.coupled.family.Ω) : ℝ :=
  coneScale γ γ (fun t => D.B t ω) (fun t => D.B' t ω) b

/-- The γ-LQG area `μ_h = A^γ_h` of the cone field. -/
def area (ω : M.coupled.family.Ω) : Measure ℂ := lqgArea γ (D.field ω)

end ConeRealization

/-! ### Joint scaling as printed, and the SLE-dependent bundle fields -/

/-- **Joint-scaling identity:** for every `b > 0`,
`(h_b, η^b) =d (h, η)`, where `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b` and `η^b = R_b⁻¹ η(b ·)`; stated as equality of
the probabilities of every measurable set of (field, curve) pairs (no `Measure.map` junk).
Sources: [14, Prop 4.13(i)] for the field and [18, §3.3] for the joint law.
The proof combines dilation invariance of whole-plane space-filling SLE (`igMap`),
independence from `h` (`indep_curve`), area parametrization (`areaParam`), and
the SLE-free area-scaling law `AreaScalingLaw`. -/
def Prop23JointScaling {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∀ b : ℝ, 0 < b → ∀ S : Set (LQGMetric.DistC × C(ℝ, ℂ)), MeasurableSet S →
    M.coupled.family.P {ω | (coneRescaleField γ (D.scale b ω) b (D.field ω),
        coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈ S} =
      M.coupled.family.P {ω | (D.field ω, D.curve ω) ∈ S}

/-- **Boundary-length covariance** (the coupling field `boundaryLength`):
`bm` is a measurable functional `BL` of `(h, η)` (DMS Theorem 1.9: `(L, R)` is the boundary-length process of
`(h, η)`), and under the rescaling of quantum lengths scale by `b^{-1/2}`
when areas scale by `b⁻¹`, so `BL(h_b, η^b) = b^{-1/2} bm(b ·)` a.s. -/
def BoundaryLengthCovariance {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∃ BL : LQGMetric.DistC × C(ℝ, ℂ) → MatedCRT.Path2, Measurable BL ∧
    (∀ᵐ ω ∂M.coupled.family.P, M.coupled.bm ω = BL (D.field ω, D.curve ω)) ∧
    ∀ b : ℝ, 0 < b → ∀ᵐ ω ∂M.coupled.family.P,
      BL (coneRescaleField γ (D.scale b ω) b (D.field ω), coneRescaleCurve (D.scale b ω) b (D.curve ω)) =
        brownRescale b (M.coupled.bm ω)

/-- **Area parametrization of space-filling SLE:** `η(0) = 0` and
`A^γ_h(η([s, t])) = t − s` for `s ≤ t`. This combines the coupling's `areaParam`
and `spaceFilling` fields. -/
def AreaParametrization {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∀ᵐ ω ∂M.coupled.family.P, D.curve ω 0 = 0 ∧ ∀ s t : ℝ, s ≤ t →
    D.area ω (D.curve ω '' Icc s t) = ENNReal.ofReal (t - s)

/-! ### SLE-free inputs (to prove) -/

/-- **Area scaling law of the cone:** for every `b > 0`,
`b⁻¹ μ_h(B_{R_b}(0))` has the law of `μ_h(B_1(0))`. Sources: `μ_{h_b}(A) = b⁻¹ μ_h(R_b A)`
a.s. for all Borel `A` ([SW] Sheffield–Wang Thm 1.1/1.4, `1605.06171v2.`, the random-dilation
coordinate change; note [17] prints this formula inverted, the area-scaling discussion), and `h_b =d h`
([14, Prop 4.13(i)]; [17] (2.8)) applied to the measurable
functional `h ↦ μ_h(B_1(0))`. No SLE is involved (GFF, circle averages, GMC). -/
def AreaScalingLaw {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∀ b : ℝ, 0 < b → ∀ S : Set ℝ≥0∞, MeasurableSet S →
    M.coupled.family.P {ω | ENNReal.ofReal b⁻¹ * D.area ω (ball 0 (D.scale b ω)) ∈ S} =
      M.coupled.family.P {ω | D.area ω (ball 0 1) ∈ S}

/-- **GMC moment of the cone's unit disk** (SLE-free, to prove): [16, Lemma A.3] with
`α = γ` and `ε = 1`: for `0 < p < min{4/γ², (2/γ)(Q − γ)} = 4/γ² − 1`, `E[μ_h(B_1(0))^p] < ∞`; together with the
measurability of the random variable `μ_h(B_1(0))` presupposed by the expectation. The moment argument uses
dyadic annuli, [DS11, Prop 2.1] at fixed dilations, Gaussian circle averages, and [RV14,
Thm 2.11]). -/
def AreaBallMoment {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  AEMeasurable (fun ω => D.area ω (ball 0 1)) M.coupled.family.P ∧
    ∀ p : ℝ, 0 < p → p < 4 / γ ^ 2 - 1 → ∫⁻ ω, D.area ω (ball 0 1) ^ p ∂M.coupled.family.P < ⊤

/-- The **raw scaled-grid event** (the body of `CellularEmbedding.ScaledGridControl`,
transported by the joint-scaling identity) for a multigraph `G` on `ℤ` and an arbitrary cell map `J`; for a cellular embedding
`H` it is `H.ScaledGridControl` (`scaledGridControl_iff_raw`). -/
def RawScaledGridControl {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) (R ε χ β q ρ p : ℝ) : Prop :=
  (∀ x, (J x ∩ ball 0 (ρ * R)).Nonempty → diam (J x) ≤ R * ε ^ q) ∧
    ∀ m n k : ℤ, (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) ∈ ball (0 : ℂ) (ρ * R) →
      R * ε ^ β ≤ R * ε ^ χ * k → R * ε ^ χ * k ≤ ρ * R →
      ball (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (2 * (R * ε ^ χ * k)) ⊆
        ball (0 : ℂ) (ρ * R) →
      ∀ x ∈ verticesMeeting J
          (sphere (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (R * ε ^ χ * k)),
        ENNReal.ofReal p ≤ G.walkLaw x {ω | G.AnnularEvent J
          (((R * ε ^ χ : ℝ) : ℂ) * ((m : ℂ) + (n : ℂ) * Complex.I)) (R * ε ^ χ * k) (G.vertexPath ω)}

theorem scaledGridControl_iff_raw {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (R ε χ β q ρ p : ℝ) :
    H.ScaledGridControl R ε χ β q ρ p ↔ RawScaledGridControl G H.cell R ε χ β q ρ p := Iff.rfl

/-- The data event "the mesh-`2^{-k}` configuration of `(bm, η)` satisfies the scaled-grid estimate event at scale 1":
`G^{2^{-k}}(bm)` is locally finite and `RawScaledGridControl` holds for it with the cells `η([2^{-k}(x−1), 2^{-k}x])`. -/
def meshGridGood (k : ℕ) (χ β q ρ p : ℝ) : Set (MatedCRT.Path2 × C(ℝ, ℂ)) :=
  {d | ∃ hlf : MatedCRT.IsLocallyFinite (CellFamily.mesh k) d.1,
    RawScaledGridControl (MatedCRT.graph (CellFamily.mesh k) d.1 hlf) (meshCells (CellFamily.mesh k) d.2)
      1 (CellFamily.mesh k) χ β q ρ p}

/-- **Measurability of the scaled-grid estimate data event** (SLE-free technical input, to prove): the mesh-`2^{-k}` event
is a Borel set of `(bm, η) ∈ Path2 × C(ℝ, ℂ)`. It is countably determined (integer grids and vertices; the walk law of
`G^ε(bm)` is a countable sum of products of transition probabilities, each a Borel function of `bm`; cell
intersections with closed sets are closed conditions in `η`). It is genuinely needed: the joint-scaling identity's equality in law
transfers only measurable sets of the data. This concerns measurability in the path and curve data;
it does not require sample-space measurability of the mesh event. -/
def MeshGridEventMeasurable : Prop :=
  ∀ (k : ℕ) (χ β q ρ p : ℝ), MeasurableSet (meshGridGood k χ β q ρ p)

/-! ### Produced downstream -/

/-- **Eventual unit-cell diameter bound** (clause (1) of the unit-scale scaled-grid event): a.s.,
for all large `k`, every unit cell meeting `B_{ρR_{2^k}}(0)` has diameter at most `R_{2^k} 2^{-qk}`. Producer: the mesoscopic construction's
`matedCRTUnitMesoscopicInput_of_interfaces` (its `hEventuallyScaled`, from `MatedCRTProposition23GridScalingInput`,
the scaled-grid estimate and Borel–Cantelli; `unitCellDiamEventually_of_scaledGrid` converts it). Needed for the cell-count bound
as printed (cells meeting the ball may protrude; the cell-counting argument, Details D.3). -/
def UnitCellDiamEventually {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ) : Prop :=
  ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop, ∀ x : ℤ,
    ((M.unitEmbedding ω).cell x ∩ ball 0 (M.ρ * M.radius ω k)).Nonempty →
      diam ((M.unitEmbedding ω).cell x) ≤ M.radius ω k * ((2 : ℝ) ^ (-(k : ℝ))) ^ M.q

/-- The eventual unit-scale scaled-grid event (in the exact form `hEventuallyScaled` of
`MesoModel.matedCRTUnitMesoscopicInput_of_interfaces`) gives `UnitCellDiamEventually`. -/
theorem unitCellDiamEventually_of_scaledGrid {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ) {χ β p₀ : ℝ}
    (h : ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop,
      (M.unitEmbedding ω).ScaledGridControl (M.radius ω k) ((2 : ℝ) ^ (-(k : ℝ))) χ β M.q M.ρ p₀) :
    UnitCellDiamEventually M := by
  filter_upwards [h] with ω hω
  filter_upwards [hω] with k hk
  exact hk.1

end MatedCRTHarmonic.CellScaling
