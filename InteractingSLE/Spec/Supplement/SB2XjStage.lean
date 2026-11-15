/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XhFill
import InteractingSLE.Spec.Supplement.SB2XiPrefix

/-!
# (G1) at one stage: the domain-chart clause from the lift of B's prefix

Packet PROVE-T14-SB2LIFT (round 25). **`isDomainChart_stage_of_lift`**: let `cℓ`, `c`, `c₁` be domain charts of
`ℍ \ fill B` (B's stage chart), `ℍ \ fill A` (the upper chart, with boundary limits `ĝ` near the identity) and
`ℍ \ fill Rel` (the relative run chart). If the relative prefix is the lift image of B's prefix
(`prefix_lift_of_steps`) through a tail lift curve, B's prefix lies on `β₀` and B's head lies in `hullK A`
(`SB2JyHull.sb2LowerHeadHull`), then the relative chart in B's stage coordinates is a domain chart of the complement of
the retained set `A ∪ B` — the domain-chart clause of `StageChainAtR`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Lk

/-- **(G1) at one stage.** -/
theorem isDomainChart_stage_of_lift {cℓ c c₁ : Chart} {A B Rel : Set ℂ} {m R : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    {ĝ : ℂ → ℂ} (hℓ : IsDomainChart (H \ fillH B) cℓ) (hc : IsDomainChart (H \ fillH A) c)
    (h₁ : IsDomainChart (H \ fillH Rel) c₁) (hA : IsCompact A)
    (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hRel : IsCompact Rel) (hRelH : Rel ⊆ Hbar) (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Continuous β₀)
    (hRelEq : Rel = liftImage β₀ tL γ B) (hB : IsCompact B) (hBr : B ⊆ range β₀)
    (hhead : β₀ '' Icc 0 tL ⊆ hullK A) (hcl : IsClosed (β₀ '' Ici tL)) :
    IsDomainChart (H \ stageRetained cℓ (A ∪ B)) (stageRelChart cℓ c c₁ m) := by
  have hĝc : ContinuousOn ĝ Hbar := GW1P.continuousOn_of_tendsto hĝ
  have hgg : EqOn ĝ c.2.1 H := fun w hw => by
    have hwH : w ∈ Hbar := QuantumZipper.H_subset_Hbar hw
    have : (𝓝[H] w).NeBot := GW1P.neBot_nhdsWithin_H hwH
    exact tendsto_nhds_unique (hĝ w hwH) ((hc.1.1.continuousOn w hw).tendsto)
  have hfill : fillH (A ∪ (fun y => ĝ (y - (m : ℂ))) '' Rel) = fillH (A ∪ B) := by
    rw [hRelEq, image_ext_liftImage hγ hĝ B]
    exact fillH_tail_eq hβ hA hB hBr hhead hcl
  exact isDomainChart_stageRelChart_of_fill hℓ hc h₁ hA hĝc hgg hC hRel hRelH hfill
    (fillH_mono subset_union_right)

end InteractingSLE.Theorem14.SB.Mn
