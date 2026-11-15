/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XiPrefix
import InteractingSLE.Spec.Supplement.SB2XzArc

/-!
# The relative prefix as the lift image, connector form

Packet PROVE-T14-SB2LIFT (round 30; the corrected T bundle, handoff §R29.3): `prefix_lift_of_stepsW`.
The statements and proofs are those of the landed originals, with `tail` replaced by its connector form
`TailArc` (`SB2XzArc`); the full `tail` is false (handoff §R29.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The relative prefix at a lockstep stage is the lift image of B's prefix.** -/
theorem prefix_lift_of_stepsW (hι : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o a₀ M : ℕ}
    (hpar : o % 2 = 0)
    (hlen : ∀ i, a₀ ≤ i → i < M → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hca₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (a₀ + o)) (ExplState.run κ b₂ J₂
        (boundaryWalkSpec b₂ J₂ θ true) D₂ a₀))
    (hstep : ∀ i, a₀ ≤ i → i < M → StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι R (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i +
            o)) (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (hMa : a₀ ≤ M) (hMlen : M + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hstart : statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ a₀) = liftImage β₀ tL γ
        (statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (a₀ + o))))
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x) :
    SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) := by
  have hacc := accCorr_run_of_steps (L := LiftRel β₀ tL γ) hι le_rfl o a₀ M hpar hlen hca₀ hstep M hMa le_rfl
  show statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) = liftImage β₀ tL γ
      (statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)))
  refine statePhysicalSet_eq_liftImage_of_accCorr hacc hstart fun X hX a ha => ?_
  refine liftImage_ofRealW hβ hβL hγ0 hι.map_base hhead
    (htail.of_mem (n := M + o) (hX ▸ List.mem_append_right _ ha)) hray fun x hx _ => ?_
  rw [hβr]
  refine prefix_subset_physSet D₁ (n := M + o) hMlen ?_
  show (x : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))
  exact Or.inr (mem_iUnion₂.2 ⟨a, hX ▸ List.mem_append_right _ ha, x, hx, rfl⟩)

end InteractingSLE.Theorem14.SB.Lk
