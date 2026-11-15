/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkLaterSeedMain
import InteractingSLE.Spec.Supplement.GW2aConnLaw

/-! # Positive finite walk exits have blocked original seeds

The general two-ray invariant of GW2a applies to every boundary word, and
does not prescribe the side of an exit or require an ambient height bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkRecordSeed

open Exist.Staged Exist.StagedLaw WalkSeedFinite WalkLaterSeed
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- At a positive finite full-lifetime launch, the original bad height on
the actual threshold side blocks its seed. A dead outcome is terminal. -/
theorem seedBlocked_launch_of_threshold_heights {κ θ : ℝ} {b : ℝ → ℝ}
    (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (hz : D.2 ≠ 0) (hfin : D.2 ≠ ⊤)
    (hR : stStatus (ExplState.launch s k D θ ⊤) = stThr (some true) →
      rightLim b (stRecR (ExplState.launch s k D θ ⊤)) + θ * chiC κ ≤ -sleLambda κ)
    (hL : stStatus (ExplState.launch s k D θ ⊤) = stThr (some false) →
      sleLambda κ ≤ leftLim b (stRecL (ExplState.launch s k D θ ⊤)) + θ * chiC κ) :
    SeedBlocked κ b θ (ExplState.launch s k D θ ⊤) := by
  rcases GW1W.launch_status_of_pos (s := s) (k := k) (θ := θ) hfin hz with hs | hs | hs
  · right
    intro ha
    have hbad := hR hs
    have hgood := ha.2
    rw [heights_eq, hs] at hgood
    change -sleLambda κ < rightLim b (stPt (ExplState.launch s k D θ ⊤)) + θ * chiC κ at hgood
    rw [(GW1W.launch_thr_true hfin hs).2.2.1] at hgood
    exact (not_lt_of_ge hbad) hgood
  · right
    intro ha
    have hbad := hL hs
    have hgood := ha.1
    rw [heights_eq, hs] at hgood
    change leftLim b (stPt (ExplState.launch s k D θ ⊤)) + θ * chiC κ < sleLambda κ at hgood
    rw [(GW1W.launch_thr_false hfin hs).2.2.1] at hgood
    exact (not_lt_of_ge hbad) hgood
  · exact Or.inl (Or.inr hs)

/-- The general invariant supplies the good stage facts simultaneously at
all walk instructions, with neither a side bound nor a prescribed exit side. -/
theorem ae_all_stageGood {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, ∀ k, GW2aConn.StageGood κ b jumps (boundaryWalkSpec b jumps θ right) E k ω := by
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨β, Y, βt, Yt, hW, -, hI⟩ := GW2aConn.exists_inv hκ hb hh rfl rfl hE hreg k
  exact GW2aConn.ae_stage hκ hb hh rfl hE hreg hW (hI.mono fun _ hω => hω.1)

/-- All positive finite later exits are now proved, even for off-sector
words. Zero-lifetime later launches are a separate remaining issue. -/
theorem ae_positiveLaterExitSeedData {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, PositiveLaterExitSeedData κ b jumps θ right (fun j => E j ω) := by
  filter_upwards [ae_all_stageGood hκ hb hh hE hreg] with ω hω
  intro k _ hk hz hfin
  have hgood := hω k hk
  rw [GW1W.instrAngle_walk hk] at hgood
  rw [GW1W.launch_walk hk] at hgood ⊢
  exact seedBlocked_launch_of_threshold_heights _ k (E k ω) hz.ne' hfin
    (fun hs => (hgood.2.1 hs).1) (fun hs => (hgood.2.2.1 hs).1)

end InteractingSLE.Theorem14.WalkRecordSeed
