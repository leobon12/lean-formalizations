/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkLaterSeed

/-! # Active-word seed admissibility rules out zero-lifetime launched pieces

The flow-line law is taken under the actual retained-past kernel and then
transferred back to the original probability measure. No original-height
identification for a later chart is assumed implicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkLaterSeed

open Exist Exist.Staged Exist.StagedLaw Restart WalkFirstSeed
open PiecewiseConstantBoundaryData (leftLim rightLim)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- Admissibility of the actual stage witness's word excludes zero lifetime
at this launch, under the original law. This applies to any walk stage. -/
theorem ae_nonzero_stage_of_seed (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ right) E k β Y)
    (hseed : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → (E k ω).2 ≠ 0 := by
  have h𝒢 : pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) E k ≤ mΩ := hE.2.1 k
  have hLp := GW1W.measurableSet_pastSigma_launch (κ := κ) hb
    (boundaryWalkSpec b jumps θ right) hE.1 hreg k
  have hZm : MeasurableSet {ω | (E k ω).2 ≠ 0} :=
    (measurableSet_eq_fun (measurable_snd.comp (hE.1 k)) measurable_const).compl
  refine Sec5.Lemma56Stages.ae_imp_of_ae_condExpKernel h𝒢 hLp hZm ?_
  filter_upwards [GW1W.ae_isFlowLineDriver_stage hκ hb hh hE hreg hW, hseed] with ω₀ hfl₀ hA₀
  intro hl₀
  obtain ⟨⟨h', hfl⟩, -⟩ := hfl₀ hl₀
  rw [GW1W.instrAngle_walk hl₀] at hfl
  filter_upwards [ae_seed_test_of_isFlowLineDriver hκ hfl] with ω ht hz
  exact ht.1 hz (hA₀ hl₀)

/-- Conversely, nonzero lifetime at a launched stage forces admissibility of
every actual witness's word. The launch event belongs to the retained past. -/
theorem ae_stage_seed_of_nonzero (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ right) E k β Y)
    (hnz : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → (E k ω).2 ≠ 0) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ := by
  have h𝒢 : pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) E k ≤ mΩ := hE.2.1 k
  have hLp := GW1W.measurableSet_pastSigma_launch (κ := κ) hb
    (boundaryWalkSpec b jumps θ right) hE.1 hreg k
  filter_upwards [GW1W.ae_isFlowLineDriver_stage hκ hb hh hE hreg hW,
    Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hnz,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp] with ω₀ hfl₀ hnzK hmem
  intro hl₀
  obtain ⟨⟨h', hfl⟩, -⟩ := hfl₀ hl₀
  rw [GW1W.instrAngle_walk hl₀] at hfl
  apply (eventually_const (f := ae (condExpKernel P
    (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) E k) ω₀))).1
  filter_upwards [ae_seed_test_of_isFlowLineDriver hκ hfl, hnzK, hmem hl₀] with ω ht hnon hl
  exact ht.2 (hnon hl)

/-- At a specified stage witness, the active-word seed condition is exactly
the exclusion of zero lifetime at launches, under the original measure. -/
theorem ae_stage_seed_iff_nonzero (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ right) E k β Y) :
    (∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ) ↔
    (∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → (E k ω).2 ≠ 0) :=
  ⟨ae_nonzero_stage_of_seed hκ hb hh hE hreg hW, ae_stage_seed_of_nonzero hκ hb hh hE hreg hW⟩

/-- An explicit sufficient input for later nonzero lifetimes: stage witnesses
whose own conditional words have admissible seeds at actual later launches.
The original-seed theorem alone does not prove this predicate. -/
def LaterStageSeedData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ k, 0 < k → ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
    IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ right) E k β Y ∧
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
          (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ

/-- Countable intersection transfers the stagewise result to all actual
later launches on one conull event. -/
theorem ae_noZeroLaterLaunchData_of_stageSeeds (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hS : LaterStageSeedData κ b jumps θ right P h E) :
    ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right (fun j => E j ω) := by
  change ∀ᵐ ω ∂P, ∀ k, 0 < k →
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → (E k ω).2 ≠ 0
  refine ae_all_iff.2 fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Eventually.of_forall fun _ hk0 => (Nat.lt_irrefl 0 hk0).elim
  · obtain ⟨β, Y, hW, hseed⟩ := hS k hk0
    exact (ae_nonzero_stage_of_seed hκ hb hh hE hreg hW hseed).mono fun _ hω _ => hω

/-- The staged-law construction supplies witnesses without a side-height
bound. Under nonzero later lifetimes their seeds are admissible. -/
theorem stageSeeds_of_ae_noZeroLaterLaunchData (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hnz : ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right (fun j => E j ω)) :
    LaterStageSeedData κ b jumps θ right P h E := by
  intro k hk0
  obtain ⟨β, Y, hW⟩ := stageLaw_iff.1 (stageLaw (GW1W.isStopLaw_stopWord hκ) runMeasStatement
    hκ hb hh k (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j))
  refine ⟨β, Y, hW, ae_stage_seed_of_nonzero hκ hb hh hE hreg hW ?_⟩
  exact hnz.mono fun _ hω => hω k hk0

/-- The active-word and lifetime formulations of the missing seed input are
equivalent, including the existence of all the required stage witnesses. -/
theorem laterStageSeedData_iff (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    LaterStageSeedData κ b jumps θ right P h E ↔
      ∀ᵐ ω ∂P, NoZeroLaterLaunchData κ b jumps θ right (fun j => E j ω) :=
  ⟨ae_noZeroLaterLaunchData_of_stageSeeds hκ hb hh hE hreg,
    stageSeeds_of_ae_noZeroLaterLaunchData hκ hb hh hE hreg⟩

end InteractingSLE.Theorem14.WalkLaterSeed
