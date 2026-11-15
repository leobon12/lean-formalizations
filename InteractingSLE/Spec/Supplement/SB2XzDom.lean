/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XlDom
import InteractingSLE.Spec.Supplement.SB2XzGlue

/-!
# The stage chart is a domain chart, connector form

Packet PROVE-T14-SB2LIFT (round 30; the corrected T bundle, handoff §R29.3): `isDomainChart_stage_of_bundlesW`.
The statements and proofs are those of the landed originals, with `tail` replaced by its connector form
`TailArc` (`SB2XzArc`); the full `tail` is false (handoff §R29.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}

/-- **(G1) at one sample**: the domain-chart clause of the per-stage correspondence at every launching relative stage
`j ≥ 2` of positive lifetime. -/
theorem isDomainChart_stage_of_bundlesW (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
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
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)
    {c : Chart} {m : ℝ} {A : Set ℂ} {ĝ : ℂ → ℂ} {Cg : ℝ} (hc : IsDomainChart (H \ fillH A) c) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) (hCg : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ Cg)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hhead : β₀ '' Icc 0 tL ⊆ hullK A) :
    ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ), 2 ≤ j →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j = some (c₁, θ') → (D₂ j).2 ≠ 0 →
      IsDomainChart (H \ stageRetained (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
          (A ∪ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o)))
        (stageRelChart (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o))) c c₁ m) := by
  intro j c₁ θ' hj hl hz
  have hl' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl]; simp
  have hl₁ := actual_launch_of_bundlesW hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS j hl' hz
  obtain ⟨⟨c₀, θ₀⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
  have hnot₁ := WalkIntRunChron.not_done_of_launch _ D₁ hl₁'
  have hnot₂ := WalkIntRunChron.not_done_of_launch _ D₂ hl
  obtain ⟨-, -, hc₁⟩ := eq_launch_of_launches (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hl
  have hℓ := Lw.isDomainChart_runChart (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ (j + o) hnot₁
  have h₁ : IsDomainChart (H \ fillH (SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j)) c₁ := by
    rw [hc₁]
    exact Lw.isDomainChart_runChart (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hR.reg₂ j hnot₂
  have hB := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ (j + o) hnot₁
  have hRelEq := prefix_lift_of_bundlesW hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS j hj hl'
  have hRel := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b₂) (jumps := J₂) _ D₂ hR.reg₂ j hnot₂
  have hRelH : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ j ⊆ Hbar := by
    rw [hRelEq]
    rintro _ ⟨s, -, rfl⟩
    exact hγp.2.2.1 s
  have hk₁ := (GW1W.even_of_launches_walk hl₁).2
  have hBr : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o) ⊆ range β₀ := by
    rw [hC.range_eq]
    exact prefix_subset_physSet D₁ (n := j + o) hk₁.le
  have hcl : IsClosed (β₀ '' Ici tL) := (isClosedEmbedding_of_isProperCurve hβp).isClosedMap _ isClosed_Ici
  exact isDomainChart_stage_of_lift hℓ hc h₁ hA hĝ hCg hRel hRelH hγ hβp.1 hRelEq hB hBr hhead hcl

end InteractingSLE.Theorem14.SB.Mn
