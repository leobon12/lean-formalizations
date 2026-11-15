/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedStage

/-!
# S3: schedule side heights at physical interior landings

The same actual conditional word works for every real recentering of the
retained chart. This includes an entry chart once its real translation is
identified. No initial boundary-value bound or schedule-angle restriction
is needed for the provenance statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- An actually launched schedule side has an angle from that schedule. -/
theorem StageSide.sideH {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x₀ : ℝ} {gw2 : Bool} {τ₀ : ℝ≥0} {l : List (ℝ × ℝ≥0)}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {v : ℝ}
    (hv : StageSide κ b jumps (x₀, gw2, scheduleProgram τ₀ l) D k v) : Lh.SideH κ l v := by
  obtain ⟨j, -, hlaunch, he⟩ := hv
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlaunch
  have hsp := (eq_launch_of_launches _ _ hcθ).1
  obtain ⟨p, hp, hpθ⟩ := Lu.exists_mem_of_scheduleProgram_getElem? τ₀ l j hsp
  have hangle : instrAngle (x₀, gw2, scheduleProgram τ₀ l) j = θ := by
    unfold instrAngle
    rw [hsp]
  rw [hangle, hpθ] at he
  exact ⟨p, hp, he⟩

/-- Actual conditional words with physical side labels, simultaneously in
every real recentering, under exactly the source's R51 regularity. -/
theorem exists_scheduleWitness_interiorSideH_reg {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {x₀ : ℝ} {gw2 : Bool} {τ₀ : ℝ≥0}
    {l : List (ℝ × ℝ≥0)} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E)
    (hR : StagedPiecesRegular κ b jumps P (x₀, gw2, scheduleProgram τ₀ l) E) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
        (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        (β ω).IsSorted ∧ ∀ a y : ℝ, y ∉ (BoundaryWord.shiftW a (β ω)).jumps →
          LuM.bdVal ((ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
            (fun j => E j ω) k).2.2.2.2.1.recenter a) (y : ℂ) ∈ H →
          Lh.SideH κ l ((BoundaryWord.shiftW a (β ω)).fn y) := by
  obtain ⟨β, Y, hW, hSide⟩ := exists_stageWitness_interiorStageSides_reg hκ hb hh hE hR k
  refine ⟨β, Y, hW, ?_⟩
  filter_upwards [hSide, GW1W.regLaunches_of_stagedPiecesRegular hR] with ω hs hr hlaunch
  refine ⟨(hs hlaunch).1, fun a y hy hyH => ?_⟩
  have hB := GW1WalkFinish.hasBdryLimits_chart_run _ _ hr k
  rw [bdVal_recenter_real hB] at hyH
  have hyJ : y + a ∉ (β ω).jumps := by
    intro h
    apply hy
    rw [BoundaryWord.jumps_shiftW]
    exact Finset.mem_image.2 ⟨y + a, h, by ring⟩
  rw [BoundaryWord.fn_shiftW]
  exact ((hs hlaunch).2 (y + a) hyJ hyH).sideH

end InteractingSLE.Theorem14.SB.S3
