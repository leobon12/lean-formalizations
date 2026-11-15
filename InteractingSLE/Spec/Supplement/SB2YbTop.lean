/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtT
import InteractingSLE.Spec.Supplement.SB2YbAE

/-!
# The relative physical set at an infinite start piece of the bundle, connector form

Packet PROVE-T14-SB2LIFT (round 31; decision D36): `range_eq_physSet_of_topVW`.
The statements and proofs are those of the landed originals, with `tail` replaced by its connector form
`TailArc` (`SB2XzArc`, read only on connectors of the actual run); the full `tail` is false (handoff
§R29.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ}

/-- **The range identity at one sample at an infinite start piece** (`PieceStartV`, `N = 1`). -/
theorem range_eq_physSet_of_topVW (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hC : CurveInputsW κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hP : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) (htop : (D₁ o).2 = ⊤)
    (hlh : NoLeftHit κ b₁ J₁ θ D₁ o) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  have hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
    rw [hP.launch, launches_launch, Function.update_self]; simp
  exact range_eq_physSet_of_piece_topW hι (N := 1) hP.even hP.launch htop hP.tip hP.pt hP.recLe hP.top hP.zero
    hP.hitR (hlh hl) hP.hitL₂ hP.lift₀ hP.memR le_rfl (fun i hi hiN => absurd hiN (by omega))
    (by have := hP.len.1; omega) (by have := hP.len.2; omega) hC.range_eq hC.inj hC.visit hC.lift_zero hC.head
    hC.tail hC.ray hP.head

end InteractingSLE.Theorem14.SB.Lk
