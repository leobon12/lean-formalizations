/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MdSeg

/-!
# `FillCorr` from GW1's chain facts and the lift images

Packet PROVE-T14-SB2LIFT (round 18). `fillCorr_of_runs` (round 17) with its walk-segment inputs discharged by GW1's
chronological arc histories (`isWalkSeg_prefix_succ_of_chain`, `isWalkSeg_partPrefix_of_chain`) and its "not done"
inputs by the launches (`WalkIntRunChron.not_done_of_launch`):

* **`fillCorr_of_chain`**: `FillCorr` at a pair of corresponding launches. It takes:
  - the run facts of both walks (regular launches, record invariants up to the launch, no left moves, finite
    lifetimes);
  - GW1's per-step facts of the actual walk (`WalkChainFacts`, almost surely by `sb2LowerWalkSegInputs`);
  - the curve facts (`LiftCurveData`, `range β₀` the walk, `β₀ t_L = R` visited by the launch stage, the program
    length);
  - the record correspondence;
  - the relative prefixes equal to the lift images of the actual ones, after the launch and at matching times of the
    two pieces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **`FillCorr` from GW1's chain facts, the run facts of both walks and the lift images.** -/
theorem fillCorr_of_chain {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβ0 : β₀ 0 = 0)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, NoLeftMove κ b₁ J₁ θ D₁ k) (hn₁ : n₁ + 1 ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, NoLeftMove κ b₂ J₂ θ D₂ k)
    (hP₂eq : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hmatch₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r))
    (hmatch₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r)) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  have hst₁ := WalkIntRunChron.not_done_of_launch _ D₁ hl₁
  have hst₂ := WalkIntRunChron.not_done_of_launch _ D₂ hl₂
  have hseg := isWalkSeg_prefix_succ_of_chain hW₁ hl₁ hfin₁ hn₁ hβr hβ0
    (GW1Z.prefixPhysSet_subset_succ _ D₁ n₁ hL)
  exact fillCorr_of_runs hι hβ hD hRa hrecc hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hseg hP₂eq
    (fun r hr0 hr => isWalkSeg_partPrefix_of_chain hP₁ hW₁ hl₁ hfin₁ hn₁ hr0 hr.le hβr hβ0 hL) hmatch₁ hmatch₂

end InteractingSLE.Theorem14.SB.Lk
