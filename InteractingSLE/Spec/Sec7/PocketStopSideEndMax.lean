/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCloseMax
import InteractingSLE.Spec.Sec7.PocketStopMarkedLaw

/-!
# Reference maximum laws from the constructed left pocket stop

PROVE-STRIPSYS38. The newly available `PocketStopMarked` Galmarino theorems
discharge both stop inputs of `CloseMax` for the bounded strip pocket. Only the
flow walls are field determined. The counterflow uses its frozen optional
coupling and ordinary stopping-time locality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I
  PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketUnionPt PocketStop PocketStopWallsFin

/-- The walls-plus-reference-hull law at `max (T⁰(q)) τ`, without a marked-stop
or total-information hypothesis. The reference's stopped information is retained. -/
theorem pocketStopWallsLaw_stopHull0_reference_marked
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*}
    {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W VL VR B ζ h'')
    (hκ' : 0 < κ') {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hR0 : ∀ ω, R ω 0 = 0) (hL0 : ∀ ω, L ω 0 = 0)
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (h𝓦 : 𝓦 ≤ MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX 0)
    (hRm' : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm' : ∀ t, Measurable[𝓦] fun ω => L ω t)
    (hGm : MeasurableSet[𝓦] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) (q : ℝ≥0)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0)) :
    PocketStopWallsLaw (𝓦 ⊔ hτ.measurableSpace) P A (travAll R L r η ψ)
      (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (fun ω => stopHull0 R L r (fun ω (s : ℝ) => W s.toNNReal ω) η ψ q ω ∪ regHull W ζ (τ ω) ω)
      (centredField h'' u₀') q := by
  have hc2 : ∀ i ω, Continuous ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := Fin.forall_fin_two.2 ⟨hRc, hLc⟩
  have h02 : ∀ i ω, (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω 0 = (0 : Fin 2 → ℂ) i :=
    Fin.forall_fin_two.2 ⟨hR0, hL0⟩
  have hm2 : ∀ i t, Measurable fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t :=
    Fin.forall_fin_two.2 ⟨hRm, hLm⟩
  have hdet2 : ∀ i t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t) =ᵐ[P]
        fun ω => f (centredField h u₀ ω) := Fin.forall_fin_two.2 ⟨hdetR, hdetL⟩
  have hloc2 : ∀ i, Sec6.IsEntranceHistoryLocal ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i)
      (centredField h u₀) P := Fin.forall_fin_two.2 ⟨hlocR, hlocL⟩
  have hΓe : (fun ω => negInv '' (range (R ω) ∪ range (L ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := funext fun ω => by
    rw [iUnion_range_fin_two]
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ W :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hGstop := PocketStopMarked.isMarkedStop_stopTimeM h𝓦 hWad hRm' hLm' hGm hG hA hAG
    hcfg hζA hψ hψm q
  have hS0 := PocketStopMarked.measurableSet_sup_iSup_of_locPrefixSigma h𝓦 hWad hRm' hLm' hGm hG hA hAG
    hcfg hζA hψ hψm q
  have hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) →
      PocketStopMarked.stopTimeM A R L r η ψ q ω < ⊤ := by
    intro ω hω hl
    rw [PocketStopMarked.stopTimeM, ite_eq_left ⟨hω, hl⟩]
    exact ENNReal.ofReal_lt_top
  have hW := pocketStopWallsLaw_max_reference_of_coupling hC hκ' hu₀' hX hζ (measurable_fullHist hm2)
    (measurable_negInv_walls hc2 hm2)
    (fun U D hUH hD hd Q hQ => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2
      hdet2 hloc2 U D hUH hD hd Q hQ) hT hGstop hS0 hτ
  obtain ⟨E, hEm, hEloc, hEq⟩ := hW
  refine ⟨E, hEm, hEloc, fun ω hω hl => ?_⟩
  rw [← hΓe] at hEq
  have hTm : PocketStopMarked.stopTimeM A R L r η ψ q ω = stopTime0 R L r η ψ q ω :=
    ite_eq_left ⟨hω, hl⟩
  have he := hEq ω hω hl
  dsimp only at he ⊢
  rw [hTm, ← stopHull0_eq_regHull (hcfg ω hω) (hζA ω hω) q] at he
  exact he

end InteractingSLE.Sec7.PocketStopSide
