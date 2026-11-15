/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LaunchClockParam

/-!
# GW1: a forced connector adds no conditioning information

The retained datum of a nonlaunch instruction is the fixed empty record. Appending
that record does not change the generated sigma algebra. In particular the kernel
after a walk's connector is exactly the kernel of its completed ordinary piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1RestartPair

open Exist.Staged Exist.StagedLaw

/-- A nonlaunch instruction appends a constant record to the past. -/
theorem pastSigma_succ_eq_of_noLaunch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (hn : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none) :
    pastSigma κ b jumps spec E (k + 1) = pastSigma κ b jumps spec E k := by
  apply le_antisymm
  · rw [pastSigma_eq_comap, pastSigma_eq_comap]
    let f : PastData k → PastData (k + 1) := fun u =>
      Fin.snoc u (readRec (fun _ => 0, 0, false))
    have he : pastMap κ b jumps spec E (k + 1) = f ∘ pastMap κ b jumps spec E k := by
      funext ω
      rw [pastMap_succ, readRec_retained_succ, hn ω, ite_eq_left rfl]
      rfl
    have hm : Measurable f := by
      apply measurable_pi_iff.2
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [f, Fin.snoc_last] using
          (measurable_const : Measurable fun _ : PastData k => readRec (fun _ => 0, 0, false))
      · simpa only [f, Fin.snoc_castSucc] using
          (measurable_pi_apply i : Measurable fun u : PastData k => u i)
    rw [he, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hm.comap_le
  · exact pastSigma_mono spec E (Nat.le_succ k)

/-- Every odd instruction of either boundary walk is a nonlaunch instruction. -/
theorem noLaunch_walk_odd {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1 + 1)).2.2.2.1
      (2 * n + 1) = none := by
  by_contra hn
  have hev := (GW1W.even_of_launches_walk hn).1
  omega

/-- The longer retained past at the next seed is precisely the terminal-piece past. -/
theorem pastSigma_walk_connector {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
    {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) E (2 * (n + 1)) =
      pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) E (2 * n + 1) := by
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  exact pastSigma_succ_eq_of_noLaunch _ E _ (fun ω => noLaunch_walk_odd (fun j => E j ω) n)

/-- Equality of the two conditional kernels is exact, not merely almost sure. -/
theorem condExpKernel_walk_connector {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {right : Bool} {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    ∀ ω, condExpKernel P
        (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) E (2 * (n + 1))) ω =
      condExpKernel P
        (pastSigma κ b jumps (boundaryWalkSpec b jumps θ right) E (2 * n + 1)) ω := by
  intro ω
  rw [pastSigma_walk_connector E n]

end InteractingSLE.Theorem14.GW1RestartPair
