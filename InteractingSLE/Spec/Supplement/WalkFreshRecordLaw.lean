/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkFreshRecordProgress

/-! # Restart freshness is proved for either walk and arbitrary original words -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkFreshRecord

open Exist.Staged Exist.StagedLaw WalkSeedFinite WalkLaterSeed WalkCapBlock

/-- Both records contain all earlier restart points. A surviving last round
selects a point strictly outside its predecessor's records, so it cannot
repeat any earlier positive-round point, regardless of direction changes. -/
theorem freshRestartData_of_records {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hG : LaunchRecordData κ b jumps θ right D) :
    FreshRestartData κ b jumps θ right D := by
  intro m n hm hmn hn hNS
  let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
  have hNS' : ¬ SeedBlocked κ b θ (R (2 * ((n - 1) + 1))) := by
    rw [show 2 * ((n - 1) + 1) = 2 * n by omega]
    exact hNS
  have hout := round_outside_records D hG (n := n - 1) (by omega) (by omega)
    hNS'
  have hB := recordBounds_run D hG (2 * m)
  have hGrow := recordsGrow_run D hG (m := 2 * m) (n := 2 * (n - 1)) (by omega)
  have hL : stRecL (R (2 * (n - 1))) ≤ stPt (R (2 * m)) := hGrow.1.trans hB.1
  have hR : stPt (R (2 * m)) ≤ stRecR (R (2 * (n - 1))) := hB.2.trans hGrow.2
  rw [show 2 * ((n - 1) + 1) = 2 * n by omega] at hout
  intro he
  change stPt (R (2 * m)) = stPt (R (2 * n)) at he
  rw [he] at hL hR
  exact hout.elim (fun h => (not_lt_of_ge hR) h) (fun h => (not_lt_of_ge hL) h)

/-- Freshness of original admissible restart marks has no additional
mathematical premise: the actual staged law proves the record-growth data. -/
theorem ae_freshRestartData {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, FreshRestartData κ b jumps θ right (fun j => E j ω) := by
  filter_upwards [ae_launchRecordData hκ hb hh hE hreg] with ω hω
  exact freshRestartData_of_records (fun j => E j ω) hω

/-- Only later nonzero lifetimes remain as a seed-data input. Both finite
positive exits and restart freshness have been proved from the staged law. -/
theorem ae_walkSeedData_of_noZero {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hnz : ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right (fun j => E j ω)) :
    ∀ᵐ ω ∂P, WalkSeedData κ b jumps θ right (fun j => E j ω) :=
  WalkRecordSeed.ae_walkSeedData_of_noZero_fresh hκ hb hh hE hreg hnz
    (ae_freshRestartData hκ hb hh hE hreg)

end InteractingSLE.Theorem14.WalkFreshRecord
