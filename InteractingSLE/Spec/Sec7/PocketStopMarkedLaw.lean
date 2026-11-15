/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedStop

/-!
# Theorem 1.3's `PocketStopWallsLaw` at `T⁰(q)` and `PocketStopUnionLaw` at `T(q)` with the stop inputs discharged

Packet PROVE-STRIPSYS43 (PROVE-STRIPSYS41 §5.1). PROVE-STRIPSYS41 proved `PocketStopWallsLaw` at the left end `T⁰(q)`
of the erasure fibre for the bounded change pocket (`pocketStopWallsLaw_stopHull0`) from the stop inputs `IsMarkedStop`
and `hS0` for `stopTime0`. Here the stop is the marked stop `stopTimeM` (`T⁰(q)` on the live event, `∞` elsewhere;
`PocketStopWallsLaw` constrains the stop only on the live event), whose inputs are proved in
`PocketStopMarkedStop.lean` as soon as the marks' walls σ-algebra `𝓦` is contained in the walls' information and the
null sets: `𝓦 ≤ σ(fullHist ![R, L]) ∨ 𝓕_0` (`𝓕` the counterflow's driving filtration, a usual augmentation).

* **`pocketStopWallsLaw_stopHull0_marked`**: `PocketStopWallsLaw` at `T⁰(q)`, no stop input;
* **`pocketStopUnionLaw_stopHull_strip_marked`**: Theorem 1.3's `PocketStopUnionLaw` at the right end `T(q)`;
* `nullSets_le_drivingFiltration`, `le_drivingFiltration_zero_of_le`: the `𝓦` condition for `𝓦 ≤ σ(walls) ∨ null sets`.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked

open QuantumZipper (H)
open LQGMetric (DistOn)
open WangWu (negInv)
open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopWallsFin

variable {Ω : Type*}

/-- The null sets are events of the driving filtration at time `0` (usual augmentation). -/
theorem nullSets_le_drivingFiltration [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) : Ito.nullSets P ≤ drivingFiltration P hX 0 :=
  Ito.nullSets_le_usualAugmentation _ P 0

/-- **The marks' condition for walls σ-algebras up to null sets**: `𝓦 ≤ σ(X) ∨ null sets` gives
`𝓦 ≤ σ(X) ∨ 𝓕_0`. -/
theorem le_drivingFiltration_zero_of_le {𝒳 : Type*} [MeasurableSpace 𝒳] {𝓦 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) {X : Ω → 𝒳}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ Ito.nullSets P) :
    𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ drivingFiltration P hX 0 :=
  h𝓦.trans (sup_le_sup_left (nullSets_le_drivingFiltration hX) _)

/-- **`PocketStopWallsLaw` at the left end `T⁰(q)` for the bounded change pocket, without stop inputs** (Aux. lemma
35's marked union law of the walls with the counterflow hull, rulings R67–R68): PROVE-STRIPSYS41's
`pocketStopWallsLaw_stopHull0` with the stop `T⁰(q)` taken on the live event (`stopTimeM`), whose Galmarino property
(`isMarkedStop_stopTimeM`) and `hS0` (`measurableSet_sup_iSup_of_locPrefixSigma`) are proved from the configuration,
the Jordan coordinate's point measurability and `𝓦 ≤ σ(fullHist ![R, L]) ∨ 𝓕_0`. -/
theorem pocketStopWallsLaw_stopHull0_marked
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[𝓦] A)
    (hAG : A ⊆ G) (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (q : ℝ≥0) :
    PocketStopWallsLaw 𝓦 P A (travAll R L r η ψ) (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (stopHull0 R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q := by
  classical
  have hc2 : ∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := Fin.forall_fin_two.2 ⟨hRc, hLc⟩
  have h02 : ∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i :=
    Fin.forall_fin_two.2 ⟨hR0, hL0⟩
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hdet2 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω) :=
    Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩
  have hloc2 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i) (centredField h u₀) P :=
    Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  rw [hΓe]
  refine pocketStopWallsLaw_regHull (T := stopTimeM A R L r η ψ q) hC hκ' hu₀' hX hζ (measurable_fullHist hm2)
    (measurable_negInv_walls hc2 hm2)
    (fun U G hUH hG hd B hB => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G hUH hG hd B hB)
    (fun ω hω hl => ?_)
    (isMarkedStop_stopTimeM h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
    (measurableSet_sup_iSup_of_locPrefixSigma h𝓦 hWad hRm' hLm' hGm hG hA hAG hcfg hζA hψ hψm q)
  have hT : stopTimeM A R L r η ψ q ω = stopTime0 R L r η ψ q ω := by
    unfold stopTimeM
    exact ite_eq_left ⟨hω, hl⟩
  rw [hT]
  exact ⟨ENNReal.ofReal_lt_top, stopHull0_eq_regHull (hcfg ω hω) (hζA ω hω) q⟩

/-- **Theorem 1.3's `PocketStopUnionLaw` at the right end `T(q)` for the bounded change pocket, without stop inputs**
(Aux. lemma 124 from Aux. lemma 35; PROVE-STRIPSYS41's `pocketStopUnionLaw_stopHull_strip` with the stop inputs
discharged): `pocketStopWallsLaw_stopHull0_marked`, STRIPSYS35's passage to `B ∪ R_{T⁰(q)}`, and ruling R67's
transfer to `T(q)`. -/
theorem pocketStopUnionLaw_stopHull_strip_marked
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (h𝓦m : 𝓦 ≤ mΩ) (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (q : ℝ≥0)
    (hpre : locPrefixSigma 𝓦 A (travAll R L r η ψ) q ≤ mΩ) :
    PocketStopUnionLaw 𝓦 P A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (stopHull R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ q) (centredField h'' u₀') q :=
  pocketStopUnionLaw_stopHull_of_stopHull0 hcfg hAG
    (pocketStopUnionLaw_cfPocket h𝓦m hRm' hLm' hGm (fun ω hω => (hcfg ω hω).conf) hA hAG hpre
      (pocketStopWallsLaw_stopHull0_marked hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
        hlocR hlocL h𝓦 hRm' hLm' hGm (fun ω hω => (hcfg ω hω).conf) hA hAG (fun ω hω => hcfg ω (hAG hω)) hζA
        hψ hψm q))

end InteractingSLE.Sec7.PocketStopMarked
