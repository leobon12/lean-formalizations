/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkCapBlock
import InteractingSLE.Spec.Supplement.GW1WalkExitData
import InteractingSLE.Spec.Supplement.GW1WalkExitRun

/-!
# Original seed data from the landed GW1 exit law

Packet PROVE-T14-WALKSIDE2, seed continuation. Under the original side-height
bound, the existing classified-exit law and finite completion prove all the
seed data needed for non-launch. No additional mathematical input is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkCapBlock

open Exist.Staged Exist.StagedLaw GW1WalkExit GW1WalkFinish
open PiecewiseConstantBoundaryData (leftLim rightLim)

/-- The original side-height bound used by the landed GW1 word induction. -/
def AmbientSideBound (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) : Prop :=
  if right then ∀ x : ℝ, x < 0 → x ∉ jumps → b x + θ * chiC κ < sleLambda κ
  else ∀ x : ℝ, 0 < x → x ∉ jumps → -sleLambda κ < b x + θ * chiC κ

/-- A classified exit has either finished or has an inadmissible seed for
the same angle. At a threshold the other height is the exposed side height. -/
theorem terminal_or_badSeed_of_classifiedExit {κ θ : ℝ} {b : ℝ → ℝ}
    {right : Bool} {s t : ExplState} (hC : ClassifiedExit κ b right s t)
    (hang : stAngle t = θ) :
    IsTerminal t ∨
      ¬ ExplState.IsAdmissibleSeed κ (ExplState.heights κ b t).1 (ExplState.heights κ b t).2 θ := by
  rcases hC.1 with hd | ⟨-, hOut⟩
  · exact Or.inl (Or.inl hd)
  · right
    have hnd : stStatus t ≠ stDone := by
      cases right <;> rcases hOut with hst | ⟨hst, -⟩ <;> rw [hst] <;>
        intro h <;> cases h
    have hbad := hC.2 hnd
    cases right
    · have hB : sleLambda κ ≤ leftLim b (stPt t) + θ * chiC κ := by
        simpa only [BadOutwardHeight, Bool.false_eq_true, ↓reduceIte, hang] using hbad
      rcases hOut with hst | ⟨hst, -⟩
      all_goals
        intro ha
        have hL := ha.1
        rw [heights_eq, hst] at hL
        change leftLim b (stPt t) + θ * chiC κ < sleLambda κ at hL
        exact (not_lt_of_ge hB) hL
    · have hB : rightLim b (stPt t) + θ * chiC κ ≤ -sleLambda κ := by
        simpa only [BadOutwardHeight, ↓reduceIte, hang] using hbad
      rcases hOut with hst | ⟨hst, -⟩
      all_goals
        intro ha
        have hR := ha.2
        rw [heights_eq, hst] at hR
        change -sleLambda κ < rightLim b (stPt t) + θ * chiC κ at hR
        exact (not_lt_of_ge hB) hR

/-- Actual classified exits give seed data at all launches and at the final
state. Finite completion is reused from the existing restart/counting proof. -/
theorem seedData_of_classifiedExits {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hC : ∀ k,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none →
      ClassifiedExit κ b right
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))) :
    WalkSeedData κ b jumps θ right D := by
  constructor
  · intro k hk
    refine terminal_or_badSeed_of_classifiedExit (hC k hk) ?_
    rw [GW1W.launch_walk hk]
    exact angle_launch _ _ _ _
  · exact Or.inl (Or.inl (walkCompletion_of_forwardExit D
      (forwardExit_at_rounds_of_classifiedExits hκ hb D hC)))

/-- In the original side-height sector, the staged history itself supplies
all seed data. No Theorem 1.2–1.3 input is needed for this result. -/
theorem ae_walkSeedData_of_ambient {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {right : Bool} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hamb : AmbientSideBound κ b jumps θ right) :
    ∀ᵐ ω ∂P, WalkSeedData κ b jumps θ right (fun j => E j ω) := by
  cases right
  · have hdata := ae_walkStageData_left hκ hb hh hE hreg hamb
    filter_upwards [hdata] with ω hω
    exact seedData_of_classifiedExits hκ hb (fun j => E j ω) fun k hk => (hω k hk).2.2.2
  · have hdata := ae_walkStageData_right hκ hb hh hE hreg hamb
    filter_upwards [hdata] with ω hω
    exact seedData_of_classifiedExits hκ hb (fun j => E j ω) fun k hk => (hω k hk).2.2.2

/-- The previously open non-flow-cap conclusion is proved for every staged
walk whose original data satisfy the side-height bound. -/
theorem ae_noLaunch_capSpec_of_ambient {κ θ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {right : Bool} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hamb : AmbientSideBound κ b jumps θ right)
    (ℓ : ℕ) (hℓ : ℓ ≤ (boundaryWalkSpec b jumps θ right).2.2.length)
    (hnon : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? ≠ some (Sum.inl (θ, ⊤))) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps θ right) ℓ θ 0)
        (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = none := by
  filter_upwards [ae_walkSeedData_of_ambient hκ hb hh hE hreg hamb] with ω hω
  exact noLaunch_capSpec_of_seedData (fun j => E j ω) hω ℓ hℓ hnon

end InteractingSLE.Theorem14.WalkCapBlock
