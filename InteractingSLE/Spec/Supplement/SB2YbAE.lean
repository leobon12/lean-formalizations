/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XbAE
import InteractingSLE.Spec.Supplement.SB2YbLift
import InteractingSLE.Spec.Supplement.SB2YbPiece

/-!
# The relative physical set from the bundle, connector form

Packet PROVE-T14-SB2LIFT (round 31; decision D36): `range_eq_physSet_of_bundlesW`.
The statements and proofs are those of the landed originals, with `tail` replaced by its connector form
`TailArc` (`SB2XzArc`, read only on connectors of the actual run); the full `tail` is false (handoff
§R29.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o N : ℕ}

/-- **The range identity at one sample from the lifts.** -/
theorem range_eq_physSet_of_bundlesW (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputsW κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ) (hβ0 : β₀ 0 = 0)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  rcases hS with hA | hPV
  · exact range_eq_physSet_of_lifts_arcW hι hR.cont hA.even hA.len hA.move hA.angle hA.pt hA.recLe hA.gap hA.low
      hreg₂ hA.zero₀ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁ hA.nz₁ hR.piece hR.two_le hR.len hR.len₁ hR.len₂
      hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hA.head hW₁ hβp hγp hD hβ0 hR.trLift
  · have hlne : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
      rw [hPV.launch, launches_launch, Function.update_self]; simp
    have hlen' : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
        i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length := by
      intro i hi hiN
      rcases eq_or_lt_of_le hi with h1 | h2
      · subst h1
        exact ⟨by have := hPV.len.1; omega, hPV.len.2⟩
      · exact hR.len i h2 hiN
    by_cases htop : (D₁ o).2 = ⊤
    · exact range_eq_physSet_of_piece_topW hι hPV.even hPV.launch htop hPV.tip hPV.pt hPV.recLe hPV.top hPV.zero
        hPV.hitR (hlh₁ o hlne) hPV.hitL₂ hPV.lift₀ hPV.memR (by have := hR.two_le; omega) hlen' hR.len₁ hR.len₂
        hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hPV.head
    have hP := hPV.toPieceStart htop
    refine range_eq_physSet_of_lifts_pieceW hι hR.cont hP.even hP.launch hP.tip hP.pt hP.recLe hP.top hP.zero
      hP.hitR hP.hitL₂ hP.recR hP.lift₀ hP.memR hP.recAfter hreg₂ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁
      hP.nz₁ hR.piece hR.two_le ?_ hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail
      hC.ray hP.head hW₁ hβp hγp hD hβ0 hR.trLift
    exact hlen'

end InteractingSLE.Theorem14.SB.Lk
