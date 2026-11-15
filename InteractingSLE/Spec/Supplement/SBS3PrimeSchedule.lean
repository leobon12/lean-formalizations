/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3PrimeAlphabet
import InteractingSLE.Spec.Supplement.SBS3Heights
import InteractingSLE.Spec.Supplement.SB2JLower

/-!
# S3: the alphabet of the actual conditional schedule word

Specialize the stage genealogy to the actual schedule program. Every
unmarked value is an original boundary value or a schedule side height.
There is no ambient boundary bound, seed-sign restriction or admissibility
premise. Excluding an original-real origin at an interior physical landing
still requires geometric information, not just this numerical alphabet.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- An earlier launched schedule instruction has an angle in that schedule,
so its certified stage height is a schedule side height or original data. -/
theorem StageHeight.original_or_sideH {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x₀ : ℝ} {gw2 : Bool} {τ₀ : ℝ≥0} {l : List (ℝ × ℝ≥0)}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {v : ℝ}
    (hv : StageHeight κ b jumps (x₀, gw2, scheduleProgram τ₀ l) D k v) :
    (∃ x ∉ jumps, v = b x) ∨ Lh.SideH κ l v := by
  rcases hv with h | ⟨j, -, hlaunch, he⟩
  · exact Or.inl h
  · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlaunch
    have hsp := (eq_launch_of_launches _ _ hcθ).1
    obtain ⟨p, hp, hpθ⟩ := Lu.exists_mem_of_scheduleProgram_getElem? τ₀ l j hsp
    have hangle : instrAngle (x₀, gw2, scheduleProgram τ₀ l) j = θ := by
      unfold instrAngle
      rw [hsp]
    rw [hangle, hpθ] at he
    exact Or.inr ⟨p, hp, he⟩

/-- The actual conditional-law witness for a schedule, with every unmarked
value classified. This is a numerical genealogy; it does not silently
identify an original boundary value with an old interior side. -/
theorem exists_scheduleWitness_original_or_sideH {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {x₀ : ℝ} {gw2 : Bool} {τ₀ : ℝ≥0}
    {l : List (ℝ × ℝ≥0)} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (x₀, gw2, scheduleProgram τ₀ l) E k β Y ∧
      ∀ᵐ ω ∂P,
        (ExplState.run κ b jumps (x₀, gw2, scheduleProgram τ₀ l)
          (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        ∀ y ∉ (β ω).jumps,
          (∃ x ∉ jumps, (β ω).fn y = b x) ∨ Lh.SideH κ l ((β ω).fn y) := by
  obtain ⟨β, Y, hW, hvalues⟩ := exists_stageWitness_heightOrigin hκ hb hh hE hreg k
  refine ⟨β, Y, hW, ?_⟩
  filter_upwards [hvalues] with ω hω hlaunch y hy
  exact (hω hlaunch y hy).original_or_sideH

end InteractingSLE.Theorem14.SB.S3
