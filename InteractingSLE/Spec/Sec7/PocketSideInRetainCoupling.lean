/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainUnion

/-!
# A fixed original-time joint law from the ambient optional coupling

PROVE-POCKET-SIDEIN. Fully explore a fixed finite wall family, and stop the
ambient coupling at a deterministic original time. The existing flat-clock
union theorem retains their entire ordered histories and the hull filtration.
The counterflow is not assumed to be determined by the field.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketStopWalls PocketStopWallsFin WangWu

/-- At a fixed original time the joint retained wall-hull law follows
directly from the optional coupling and Lemma 6.2 inputs of the walls. -/
theorem joint_walls_law_at_original_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    {u u' : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u) P)
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hCoupling : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h'') (hκ : 0 < κ)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (forceJumpSet xL xR) u')
    (hKilled : IsMeasurableKilledDriving W VL VR ζ) (hLife : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {n : ℕ} {η : Fin n → Ω → ℝ≥0 → ℂ} {x : Fin n → ℂ}
    (hCont : ∀ j ω, Continuous (η j ω)) (hStart : ∀ j ω, η j ω 0 = x j)
    (hMeas : ∀ j t, Measurable fun ω => η j ω t)
    (hDetermined : ∀ j t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η j ω t) =ᵐ[P] fun ω => f (centredField h u ω))
    (hLocal : ∀ j, Sec6.IsEntranceHistoryLocal (η j) (centredField h u) P) (q : ℝ≥0) :
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (fullHist η) inferInstance ⊔ drivingFiltration P hKilled q)
      (fun ω => H ∩ ((negInv '' (⋃ j, range (η j ω))) ∪ regHull W ζ q ω))
      (centredField h'' u') P := by
  have hLaw := isHistoryAvoidanceLocal_walls_regHull_stoppingTime hCoupling hκ hu' hKilled hLife
    (measurable_fullHist hMeas) (measurable_negInv_walls hCont hMeas)
    (fun V G hVH hG hMD A hA => walls_hW_counterflow hTransport hTranslate hu hu'.1 hh
      hCont hStart hMeas hDetermined hLocal V G hVH hG hMD A hA)
    (isStoppingTime_const (drivingFiltration P hKilled) q)
  have hSet : (wallsHullAt (fun ω => negInv '' ⋃ j, range (η j ω))
      (regHull W ζ) (fun _ => ((q : WithTop ℝ≥0) : ℝ≥0∞))) =
      (fun ω => H ∩ ((negInv '' (⋃ j, range (η j ω))) ∪ regHull W ζ q ω)) := by
    funext ω
    simp [wallsHullAt]
  rw [hSet] at hLaw
  simpa only [IsStoppingTime.measurableSpace_const] using hLaw

end InteractingSLE.Sec7.PocketStopSide
