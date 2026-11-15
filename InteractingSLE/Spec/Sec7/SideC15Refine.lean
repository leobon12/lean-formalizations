/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15ReadyBranch

/-!
# The ready branch refinement with its R90 normalized offset

PROVE-SIDE-COLLAR2. The actual source branch is walls-measurable. Its
positive-probability fibres are ready and cover the old test almost
surely. Each retained chart has the same source lift and a constant
compatible offset, even when the original test has no constant branch.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (chiC)
open scoped Real

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.SideC13 Sec7.SideC15

variable {Ω : Type} [MeasurableSpace Ω]

/-- R90a's complete refinement of an actual ready test. The returned
integer is measurable in the completed incoming walls, and on every
retained fibre the original source branch equals its refinement label.
The installed offset agrees with the samplewise source expression. -/
theorem exists_ready_branch_refinement {j : SideTest Ω} (i : BothLow) {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hL0 : ∀ ω, d.leftWall j.seed ω 0 = 0) (b : ℝ) :
    ∃ n : Ω → ℤ, Measurable[(j.target i d).walls] n ∧
      (∀ k : ℤ, 0 < d.measure (branchEvent j.event n k) →
        (j.refineBranch n k).Ready d ∧ ∀ ω ∈ (j.refineBranch n k).event,
          Lemma71N.IsPocketBranch (d.leftWall j.seed ω) (d.rightWall ω)
            (conjugateFlowChart (((j.refineBranch n k).target i d).baseChart ω)) k ∧
          sourceFrameOffset (16 / i.kappa) b k =
            b + 2 * π * chiC (16 / i.kappa) * (1 - (n ω : ℝ))) ∧
      (∀ᵐ ω ∂d.measure, ω ∈ j.event →
        ∃ k : ℤ, 0 < d.measure (branchEvent j.event n k) ∧ ω ∈ (j.refineBranch n k).event) := by
  obtain ⟨n, hn, hbranch⟩ := j.exists_measurable_branch_of_ready i hj hRc hLc hL0
  refine ⟨n, hn, ?_, ?_⟩
  · intro k hk
    have hn' := hn
    rw [target_walls] at hn'
    refine ⟨j.refineBranch_ready hj hn' hk, ?_⟩
    intro ω hω
    have hω' : ω ∈ branchEvent j.event n k := hω
    constructor
    · rw [j.refineBranch_baseChart i d hω, ← hω'.2]
      exact hbranch ω hω'.1
    · rw [sourceFrameOffset, hω'.2]
  · filter_upwards [ae_mem_positive_branchEvent d.measure j.event n] with ω hω hA
    exact ⟨n ω, hω hA, hA, rfl⟩

end InteractingSLE.Wire.Current.SideTest
