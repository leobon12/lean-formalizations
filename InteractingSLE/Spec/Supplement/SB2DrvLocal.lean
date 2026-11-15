/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KdInputs
import InteractingSLE.Spec.Supplement.WalkInfLocal
import InteractingSLE.Spec.Supplement.WalkLeafWire
import InteractingSLE.Spec.Supplement.WalkPastDet

/-!
# SB2(1)'s retained lower prefix is a history-marked local set

Packet PROVE-T14-SB2DRV (round 2). Every union kernel of SB2(1)'s proof ("At every rational ordinary time of the other
history, its marked union with `A` has the Gaussian local-set kernel", supplement p. 631) starts from the retained lower
prefix as a marked local set for its retained past. For the lower walk of an SB2(1) launch problem this is the gluing
`WalkInf.markedLocalAE_of_kernel` (any staged program, every number of instructions) with the field determination of
the retained pasts (`WalkLaw.pastDetRegStatement_of_thm12_thm13`) and the per-stage launch locality of the walk
(`WalkLeaf.walkStageLaunchLocalStatement_of_thm12_thm13`, `WalkLaw.walkStageKernelLocalStatement_of_launch`):

* **`walkPrefix_markedLocal`**: at every number of instructions `n`, the explored set of the lower walk (in `ℍ`) is,
  with its avoidance events in the null-completed retained past, a history-marked local set of the centred field for
  the retained past `pastSigma n`.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw

/-- **The retained lower prefix of an SB2(1) problem is a history-marked local set** for its retained past, at every
number of instructions (clause (i) up to null sets, ruling R58). -/
theorem walkPrefix_markedLocal (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (n : ℕ) :
    (∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[LocalSets.aeSigma (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) n) P]
        {ω | Disjoint (WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) n ω) U}) ∧
    (∀ᵐ ω ∂P, IsOpen (H \ WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) n ω)) ∧
    WholeField.IsHistoryAvoidanceLocal
      (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) n)
      (WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) n)
      (WholeField.centredField h u₀) P := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hS := HP.staged _ hw
  have hR := HP.pieces_regular _ hw
  have hker := WalkLaw.walkStageKernelLocalStatement_of_launch hθ
    (WalkLeaf.walkStageLaunchLocalStatement_of_thm12_thm13 h12p h13 hθ true)
  exact WalkInf.markedLocalAE_of_kernel HP.boundary HP.field hu₀ hS hR (HP.drivers_regular _)
    (fun j => WalkLaw.pastDetRegStatement_of_thm12_thm13 h12p h13 κ HP.kappa_pos HP.kappa_lt_four b jumps
      HP.boundary P h HP.field _ _ hS hR j)
    (fun j => hker κ HP.kappa_pos HP.kappa_lt_four b jumps HP.boundary P h HP.field E HP.staged HP.pieces_regular
      HP.drivers_regular u₀ hu₀ j) n

end InteractingSLE.Theorem14.SB.Lv
