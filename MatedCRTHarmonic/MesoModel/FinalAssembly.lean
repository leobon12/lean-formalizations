import Mathlib
import MatedCRTHarmonic.Frozen.MatingOfTreesInput
import MatedCRTHarmonic.Frozen.CellModelExists
import MatedCRTHarmonic.MoTInput.ConeRealization
import MatedCRTHarmonic.MoTInput.CurveAdapters
import MatedCRTHarmonic.MesoModel.FinalAdapters
import MatedCRTHarmonic.GMCFacts.LowerTail
import MatedCRTHarmonic.GMCFacts.ConeCompare
import MatedCRTHarmonic.GMCFacts.ConeMoment
import MatedCRTHarmonic.ConeScaling.AreaScalingHolds
import MatedCRTHarmonic.CellScaling.Assembly
import MatedCRTHarmonic.CellScaling.L27Bridge
import MatedCRTHarmonic.CellScaling.MeshMeasurableEvent
import MatedCRTHarmonic.CellScaling.JointScalingOFinal
import MatedCRTHarmonic.CellFamily.WaypointProof
import MatedCRTHarmonic.MesoModel.Rec
import MatedCRTHarmonic.MesoModel.MesoSkeleton
import MatedCRTHarmonic.MesoModel.Annulus38
import MatedCRTHarmonic.MesoModel.CloseCellModel

/-!
# Final cell-model assembly

The conditional cell-model theorem below has, as its only extra hypotheses, the stated probabilistic inputs:

| hypothesis | landed statement | producer |
|---|---|---|
| `hAnnulus38` | `MesoModel.Annulus38OneScaleBadBound M.coupled.family M.ρ` (per-scale [18] Lemma 3.8) | the one-scale estimate and Lemma 2.7 |
| `hREC` | `MesoModel.MatedCRTRecurrencePathScaleInput γ` | the recurrence and one-scale estimates |

Each hypothesis is quantified by `FinalForAllCouplings`: it is required only at
the realization (`MoTInput.unitMesoModelOfCoupling`, `MoTInput.coneRealizationOfCoupling`) of a mating-of-trees
coupling `D` of some `γ ∈ (0, 2)` on a standard Borel space, which is the weakest form the proof uses; a producer
proved for every model/realization closes it through `finalForAllCouplings_of_forall`.

The other inputs are supplied by the following results (`final_cellModelExists_of_coupling` is the per-coupling core):
* the waypoint input `CellFamily.WaypointStrongMarkovInputFixed2` (`waypointStrongMarkovInputFixed2_holds`);
* the cone's unit-disc area moments `CellScaling.AreaBallMoment` (`GMCFacts.areaBallMoment_holds`; [16] Lemma A.3);
* the cone's area scaling law `CellScaling.AreaScalingLaw` (`ConeScaling.areaScalingLaw_holds`; DMS
  Prop 4.13(i) and random-dilation coordinate change);
* Peanosphere/G0 (`MoTInput.ae_peanosphere`, `ae_sideStrict_allMeshes`);
* the area parametrization `CellScaling.AreaParametrization` from the v3 field `areaParam` stated for every vague limit
  and the SLE-free existence of the cone area limit (`GMCFacts.coneAreaExists_holds`), via
  `final_areaParametrization_of_reparam`;
* the boundary-length covariance from the bundle field `boundaryLength`;
* the corrected Lemma 2.7 bad-event input from the bundle's GHM15 Prop 3.4 field
  (`final_segmentsContainBalls_of_reparam`), `GMCFacts.gmcLowerTail_holds`, `GMCFacts.areaDominates_toCellModel`
  and `lemma27CellDiamBad_of_cone`;
* the corrected Lemma 3.8 bad-event input from `hAnnulus38` (`annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound`);
* `cellModelExists_of_cone` (the scaling, cell-count, annular, and mesoscopic-control estimates on the model),
  and `matedCRTRecurrenceInput_of_theorem14ScaleInput`.
No frozen theorem anchor is imported.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-! ### The quantifier of the remaining inputs -/

/-- **The quantifier of the remaining inputs.** `Q γ M C` holds at MTC's unit-mesh model
`M = MoTInput.unitMesoModelOfCoupling D hstd hγ` and cone realization `C = MoTInput.coneRealizationOfCoupling D hstd hγ`
of every mating-of-trees coupling `D` (frozen `MatedCRT.IsMatingOfTreesCoupling`) of every `γ ∈ (0, 2)` on a standard
Borel probability space, i.e. of every witness of the frozen `MatedCRT.MatingOfTreesInput γ`. -/
def FinalForAllCouplings
    (Q : (γ : ℝ) → (M : MatedCRTUnitMesoModel γ) → CellScaling.ConeRealization M → Prop) : Prop :=
  ∀ (γ : ℝ) (hγ : γ ∈ Ioo 0 2) (Ω : Type) (_ : MeasurableSpace Ω) (hstd : StandardBorelSpace Ω)
    (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
    (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2)
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
    Q γ (MoTInput.unitMesoModelOfCoupling D hstd hγ) (MoTInput.coneRealizationOfCoupling D hstd hγ)

/-! ### Landed producers at one coupling -/

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **Peanosphere/G0 at the coupling** (bundle fields `spaceFilling`, `areaParam`, `merge`, `onlyMerge`,
`boundaryLawBM`, through MTC's `MoTInput.ae_peanosphere`, `MoTInput.ae_sideStrict_allMeshes` and G0BM): the scaled-grid estimate Peanosphere input of the realization's mesh family. -/
theorem final_peanosphereG0_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    CellFamily.PeanosphereG0 (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family := by
  let M := MoTInput.unitMesoModelOfCoupling D hstd hγ
  have hpeano := MoTInput.ae_peanosphere D
  have hside := MoTInput.ae_sideStrict_allMeshes D
  have hbm := MoTInput.ae_bundleBM_eq D
  have hcurve := MoTInput.ae_bundleCurve_eq D
  intro k
  change ∀ᵐ ω ∂P, ∃ (path : MatedCRT.Path2) (curve : ℝ → ℂ)
    (h : MatedCRT.IsLocallyFinite (CellFamily.mesh k) path)
    (H : CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) path h) 0),
      RouteM.Peanosphere path curve ∧ RouteM.SideStrict (CellFamily.mesh k) path ∧
      (∀ x y, (M.coupled.family.G k ω).adj.Adj x y ↔
        (MatedCRT.graph (CellFamily.mesh k) path h).adj.Adj x y) ∧
      (∀ x, (M.coupled.family.H k ω).cell x = H.cell x) ∧
      ∀ x, H.cell x = curve '' Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)
  filter_upwards [hpeano, hside, hbm, hcurve] with ω hp hs hbmω hcurveω
  refine ⟨MoTInput.bundleBM D ω, MoTInput.bundleCurve D ω,
    (MoTInput.bundleGeometry D ω k).1, (MoTInput.bundleGeometry D ω k).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbmω, hcurveω]
    exact hp
  · rw [hbmω]
    exact hs k
  · intro x y
    rfl
  · intro x
    rfl
  · intro x
    exact congrArg (fun f : ℤ → Set ℂ => f x) (MoTInput.bundleGeometry_cell D ω k)

/-- **Area parametrization at the coupling** (the area-parametrization premise): the v3 field `areaParam` (every vague limit of the area
approximations of the γ-cone field gives the curve segments their length) with `spaceFilling`'s `ηL 0 = 0`, and the
SLE-free existence of the cone area limit (`final_areaParametrization_of_reparam`). -/
theorem final_areaParametrization_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    CellScaling.AreaParametrization (MoTInput.coneRealizationOfCoupling D hstd hγ) := by
  have hηL0 : ∀ᵐ ω ∂P, ηL ω 0 = 0 := by
    filter_upwards [D.spaceFilling] with ω hω
    exact hω.2.2.1
  exact final_areaParametrization_of_reparam (MoTInput.coneRealizationOfCoupling D hstd hγ) ηL η
    (MoTInput.ae_bundleCurve_eq D) hηL0 D.areaParam

/-- **GHM15 Prop 3.4 at the coupling**: the bundle field `segmentsContainBalls` for `ηL` gives Lemma 2.7's
`SegmentsContainBalls` for the realization's cell model, whose curve is a.s. `η = ηL ∘ φ` (`areaParam`). -/
theorem final_segmentsContainBalls_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (hpar : CellScaling.AreaParametrization (MoTInput.coneRealizationOfCoupling D hstd hγ)) :
    GMSLemma27.SegmentsContainBalls ((MoTInput.coneRealizationOfCoupling D hstd hγ).toCellModel hpar) := by
  refine final_segmentsContainBalls_of_reparam _ ηL ?_ D.segmentsContainBalls
  filter_upwards [D.areaParam, MoTInput.ae_bundleCurve_eq D] with ω hω hcω
  rcases hω with ⟨⟨φ, -, hφ⟩, -⟩
  have hc : MoTInput.bundleCurve D ω = η ω := hcω
  refine ⟨φ, fun t => ?_⟩
  change MoTInput.bundleCurve D ω t = ηL ω (φ t)
  rw [hc]
  exact hφ t

/-- **Boundary-length covariance at the coupling**: the bundle field `boundaryLength` (DMS and the
coordinate-change rule for quantum length), transported to MTC's repaired curve and Brownian path. -/
theorem final_boundaryLengthCovariance_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    CellScaling.BoundaryLengthCovariance (MoTInput.coneRealizationOfCoupling D hstd hγ) := by
  rcases D.boundaryLength with ⟨BL, hBLmeas, hBLbase, hBLscale⟩
  refine ⟨BL, hBLmeas, ?_, ?_⟩
  · filter_upwards [hBLbase, MoTInput.ae_bundleBM_eq D, MoTInput.ae_bundleCurve_eq D]
      with ω hbase hbm hcurve
    have hbm' : MoTInput.bundleBM D ω = bm ω := hbm
    have hcurve' : MoTInput.bundleCurve D ω = η ω := hcurve
    change MoTInput.bundleBM D ω =
      BL (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω), MoTInput.bundleCurve D ω)
    rw [hbm', hcurve']
    exact hbase
  · intro b hb
    filter_upwards [hBLscale b hb, MoTInput.ae_bundleBM_eq D, MoTInput.ae_bundleCurve_eq D]
      with ω hscale hbm hcurve
    have hbm' : MoTInput.bundleBM D ω = bm ω := hbm
    have hcurve' : MoTInput.bundleCurve D ω = η ω := hcurve
    change BL (CellScaling.coneRescaleField γ (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (CellScaling.coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)),
        CellScaling.coneRescaleCurve (CellScaling.coneScale γ γ (fun t => B t ω) (fun t => B' t ω) b) b
          (MoTInput.bundleCurve D ω)) =
      CellScaling.brownRescale b (MoTInput.bundleBM D ω)
    rw [hbm', hcurve']
    exact hscale

/-- **The corrected [18] Lemma 2.7 bad-event input at the coupling** (Lemma 2.7, `lemma27CellDiamBad_of_cone`):
from the bundle's GHM15 Prop 3.4 field, the GMC lower tail [GHM15 Lemma 3.12] and the whole-plane GFF area comparison
(GMCF), all landed. -/
theorem final_lemma27CellDiamBad_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    CellFamily.Lemma27CellDiamBad (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family
      (MoTInput.unitMesoModelOfCoupling D hstd hγ).q (MoTInput.unitMesoModelOfCoupling D hstd hγ).ρ := by
  have hpar := final_areaParametrization_of_coupling D hstd hγ
  exact CellScaling.lemma27CellDiamBad_of_cone (MoTInput.coneRealizationOfCoupling D hstd hγ) hpar
    (final_segmentsContainBalls_of_coupling D hstd hγ hpar) (GMCFacts.gmcLowerTail_holds hγ.1 hγ.2)
    (GMCFacts.areaDominates_toCellModel (MoTInput.coneRealizationOfCoupling D hstd hγ) hpar hγ.1 hγ.2)

/-- **`CellModelExists γ` at one coupling, from the three remaining inputs at that coupling** (the core of
`exists_cellModel_of_matingOfTrees_of_remaining`): `cellModelExists_of_cone` on MTC's model and realization,
with every other input produced above or by the waypoint construction. -/
theorem final_cellModelExists_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    (h23 : CellScaling.ConeJointScaling (MoTInput.coneRealizationOfCoupling D hstd hγ))
    (hAnnulus38 : Annulus38OneScaleBadBound (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family
      (MoTInput.unitMesoModelOfCoupling D hstd hγ).ρ)
    (hREC : MatedCRTRecurrencePathScaleInput γ) :
    MatedCRT.CellModelExists γ := by
  let M := MoTInput.unitMesoModelOfCoupling D hstd hγ
  have h26 : MatedCRTCellFamilyInterfaces M :=
    ⟨final_lemma27CellDiamBad_of_coupling D hstd hγ,
      annulus38_lemma38AnnulusHitBad_of_oneScaleBadBound M.coupled.family M.ρ hAnnulus38,
      CellFamily.waypointStrongMarkovInputFixed2_holds M.coupled.family M.q M.ρ,
      final_peanosphereG0_of_coupling D hstd hγ⟩
  exact CellScaling.cellModelExists_of_cone M (MoTInput.coneRealizationOfCoupling D hstd hγ) h23
    (final_boundaryLengthCovariance_of_coupling D hstd hγ) (final_areaParametrization_of_coupling D hstd hγ)
    (ConeScaling.areaScalingLaw_holds _) (GMCFacts.areaBallMoment_holds _)
    CellScaling.MeshGridEventMeasurable_holds h26
    (matedCRTRecurrenceInput_of_theorem14ScaleInput hREC)

end Coupling

/-! ### The two v3 theorems, conditional on the remaining inputs -/

/-- **`exists_cellModel_of_matingOfTrees` (frozen v3 type) from the remaining inputs.** CONDITIONAL on the
mating-of-trees input (as the frozen anchor itself) and on the two still-unproved inputs
`hAnnulus38`, `hREC` in their landed statements (see the module docstring for their producers). The waypoint
input, the area moments and scaling law of the cone, Peanosphere/G0, the area parametrization (the area-parametrization premise), the
boundary-length covariance and the corrected Lemma 2.7 input are supplied from landed results. -/
theorem exists_cellModel_of_matingOfTrees_of_remaining
    (hAnnulus38 : FinalForAllCouplings fun _ M _ => Annulus38OneScaleBadBound M.coupled.family M.ρ)
    (hREC : FinalForAllCouplings fun γ _ _ => MatedCRTRecurrencePathScaleInput γ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → MatedCRT.MatingOfTreesInput γ → MatedCRT.CellModelExists γ := by
  rintro γ hγ0 hγ2 ⟨Ω, mΩ, hstd, P, X, X₀, hIG₀, B, B', B₀, B₀', U, ηL, η, η₀, bm, D⟩
  have hγ : γ ∈ Ioo 0 2 := ⟨hγ0, hγ2⟩
  exact final_cellModelExists_of_coupling D hstd hγ
    (CellScaling.JointScalingO.coneJointScaling_forAllCouplings γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)
    (hAnnulus38 γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)
    (hREC γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D)

end MatedCRTHarmonic.MesoModel
