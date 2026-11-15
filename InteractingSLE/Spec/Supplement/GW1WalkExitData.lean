/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitProfile

/-! # GW1: the proved word, profile, record, and exit data at all launches -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish LQGMetric

def WalkStageData (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ k, let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
    (R (k + 1)).2.2.2.1 k ≠ none →
      OwnProfile right (R k) ∧ OwnReady right (R k) ∧
      ((D k).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D k)))) ∧
      ClassifiedExit κ b right (R k) (R (k + 1))

section Law

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem ae_walkStageData_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + θ * QuantumZipper.chiC κ < sleLambda κ) :
    ∀ᵐ ω ∂P, WalkStageData κ b jumps θ true (fun j => E j ω) := by
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨β, Y, hW, hI⟩ := GW1W.exists_witness_right hκ hb hh hE hreg hamb k
  filter_upwards [hI,
    GW1W.ae_stage_right hκ hb hh hE hreg hW (hI.mono fun ω hω hl => (hω hl).1),
    ae_classifiedExit_right hκ hb hh hE hreg hW
      (hI.mono fun ω hω hl => ⟨(hω hl).1, (hω hl).2.1⟩)] with ω hi hs hc
  dsimp only
  intro hl
  exact ⟨(hi hl).1.2.1, (hi hl).2.1, (hs hl).2.1, hc hl⟩

theorem ae_walkStageData_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ false) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + θ * QuantumZipper.chiC κ) :
    ∀ᵐ ω ∂P, WalkStageData κ b jumps θ false (fun j => E j ω) := by
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨β, Y, hW, hI⟩ := GW1W.exists_witness_left hκ hb hh hE hreg hamb k
  filter_upwards [hI,
    GW1W.ae_stage_left hκ hb hh hE hreg hW (hI.mono fun ω hω hl => (hω hl).1),
    ae_classifiedExit_left hκ hb hh hE hreg hW hI] with ω hi hs hc
  dsimp only
  intro hl
  exact ⟨(hi hl).1.2.1, (hi hl).2.1, (hs hl).2.1, hc hl⟩

end Law

theorem walkStageData_of_theorem13 (hT13₀ : Theorem13Statement.{0}) :
    WalkLocalStatement.{u} (fun κ b jumps right D =>
      WalkStageData κ b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right D) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg right
  have hamb := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀)
    hκ hκ4 hb hh hcf hζ'
  have hS := hE (GW1Z.walkSpec b jumps right)
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right)
  cases right
  · exact ae_walkStageData_left hκ hb hh hS (hreg _) hamb.2
  · exact ae_walkStageData_right hκ hb hh hS (hreg _) hamb.1

end InteractingSLE.Theorem14.GW1WalkExit
