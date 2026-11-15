/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5PhaseEngine
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefPrefix
import InteractingSLE.Spec.Sec7.PocketStopMarkedLaw

/-!
# Lemma R.5's old references for a change pocket: raw laws at original rational times

Packet PROVE-R5-PHASE. Proof of Lemma R.5 (`source/spec/p433-480.md` L1013–L1020, p. 475): "Implement the
simultaneous comparison with a countable family of rational original times […]. For each `s`, apply the nested marked
local-set law […]". The old reference at an original time `s` is the pocket exterior together with the counterflow's
(regularized) hull at `s`, with the record "both full incoming walls and the counterflow's driving history up to `s`".

* `refInfo P hX R L s` (def): that record, `σ(walls) ∨ 𝓕_s`;
* `refInfo_le`, `wallsSigma_le_refInfo`;
* **`pocketStopUnionLaw_ref`**: the raw stopped union law of the reference at relative level `0` for every change
  pocket test (bounded or opening at the flow seed) and every curve driven on the test — the input
  `hRawReference` of `R5Phase.pocketStopPhaseSideLimit_of_incrementLaws_offExc`.

The proof is the walls–hull locality at the constant stopping time `s`
(`PocketStopWallsFin.isHistoryAvoidanceLocal_walls_regHull_stoppingTime`), the zero relative prefix
(`PocketStopSide.locPrefixSigma_zero_of_driven`) and the passage from the walls to the pocket exterior
(`PocketStopField.pocketStopUnionLaw_cfPocket`). It is margin- and word-independent. Ruling R48: nothing here uses
Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Phase

open WholeField PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop PocketWordPerQ
  PocketCoord PocketJordan PocketStopSide PocketTraversal Lemma71C

variable {Ω : Type*}

/-- **The record of an original-time reference**: both full incoming walls and the counterflow's driving history
up to the original time `s`. -/
abbrev refInfo [mΩ : MeasurableSpace Ω] (P : Measure Ω) {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) (R L : Ω → ℝ≥0 → ℂ) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX s

section Record

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem refInfo_le (hX : IsMeasurableKilledDriving W VL VR ζ) {R L : Ω → ℝ≥0 → ℂ}
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t) (s : ℝ≥0) :
    refInfo P hX R L s ≤ mΩ := by
  refine sup_le (measurable_fullHist ?_).comap_le ((drivingFiltration P hX).le s)
  intro i t
  fin_cases i
  · exact hRm t
  · exact hLm t

theorem wallsSigma_le_refInfo (hX : IsMeasurableKilledDriving W VL VR ζ) (R L : Ω → ℝ≥0 → ℂ) (s : ℝ≥0) :
    wallsSigma P R L ≤ refInfo P hX R L s :=
  (wallsSigma_le_drivingFiltration hX R L).trans
    (sup_le_sup_left ((drivingFiltration P hX).mono (show (0 : ℝ≥0) ≤ s from zero_le)) _)

end Record

/-- **The raw law of an original-time reference** (Lemma R.5's old reference; R73 §3.1): for a change-pocket test
`A ⊆ G` (walls-measurable) and any curve `γ` driven on `A`, the pocket exterior together with the counterflow's hull
at the original time `s` satisfies the marked union law at relative level `0`, with record `refInfo P hX R L s`. The
inputs are exactly the walls' data of `PocketStopMarked.pocketStopWallsLaw_stopHull0_marked`. -/
theorem pocketStopUnionLaw_ref
    {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
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
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (s : ℝ≥0) :
    PocketStopUnionLaw (refInfo P hX R L s) P A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s)
      (centredField h'' u₀') 0 := by
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
  have hle := refInfo_le (P := P) hX hRm hLm s
  have hWS := wallsSigma_le_refInfo (P := P) hX R L s
  have hRm' : ∀ t, Measurable[refInfo P hX R L s] fun ω => R ω t := fun t =>
    (measurable_right_wallsSigma (P := P) hRc hLc t).mono hWS le_rfl
  have hLm' : ∀ t, Measurable[refInfo P hX R L s] fun ω => L ω t := fun t =>
    (measurable_left_wallsSigma (P := P) hRc hLc t).mono hWS le_rfl
  have hA' : MeasurableSet[refInfo P hX R L s] A := hWS _ hA
  have hpre : locPrefixSigma (refInfo P hX R L s) A γ 0 = refInfo P hX R L s :=
    locPrefixSigma_zero_of_driven hA' hγ
  have hτ := isStoppingTime_const (drivingFiltration P hX) s
  have hloc := isHistoryAvoidanceLocal_walls_regHull_stoppingTime hC hκ' hu₀' hX hζ (measurable_fullHist hm2)
    (measurable_negInv_walls hc2 hm2)
    (fun U G' hUH hG' hd B' hB' => walls_hW_counterflow hT' hTr hu₀ hu₀'.1 hh hc2 h02 hm2 hdet2 hloc2 U G' hUH hG'
      hd B' hB') hτ
  rw [IsStoppingTime.measurableSpace_const] at hloc
  have hΓe : (fun ω => negInv '' ⋃ i, range ((![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω)) =
      fun ω => negInv '' (range (R ω) ∪ range (L ω)) := funext fun ω => by
    rw [iUnion_range_fin_two]
  rw [hΓe] at hloc
  have hW : PocketStopWallsLaw (refInfo P hX R L s) P A γ (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (regHull W' ζ' s) (centredField h'' u₀') 0 := by
    refine ⟨wallsHullAt (fun ω => negInv '' (range (R ω) ∪ range (L ω))) (regHull W' ζ')
      (fun _ => (((s : WithTop ℝ≥0)) : ℝ≥0∞)), ?_, ?_, fun ω _ _ => ?_⟩
    · have hm := measurable_wallsHullAt_regHull hX (measurable_negInv_walls hc2 hm2)
        (measurable_const (a := (((s : WithTop ℝ≥0)) : ℝ≥0∞)))
      rwa [hΓe] at hm
    · rw [hpre]
      exact hloc
    · simp only [wallsHullAt]
      split_ifs with hs'
      · rfl
      · exact absurd (WithTop.coe_lt_top s) hs'
  exact pocketStopUnionLaw_cfPocket hle hRm' hLm' (hWS _ hGm) hG hA' hAG (by rw [hpre]; exact hle) hW

end InteractingSLE.Sec7.R5Phase
