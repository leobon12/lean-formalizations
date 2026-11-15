/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntGermLocal
import InteractingSLE.Spec.Supplement.WalkIntCanonCollar

/-!
# Transition-hull gaps follow from incident real intervals

If the component lies in the larger reference domain, its incident
half-disc in a smaller chart excludes the larger transition hull.
Consequently the inherited lift comparison needs no separate gap input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntGerm

open WalkIntCanon

/-- The gap needed by Aux. lemma 57 follows from a reflected incident
interval and containment of the component in the larger chart domain. -/
theorem exists_transition_gap_of_realLimits {c dA dB : Chart}
    (hc : c.IsConformal) (hdA : dA.IsConformal)
    (A : HullModel dA) (B : HullModel dB)
    (hCB : (c.dom : Set ℂ) ⊆ dB.dom) {x r u : ℝ} (hr : 0 < r)
    (hdom : ∀ z ∈ H ∩ ball (x : ℂ) r, c.2.1 z ∈ dA.dom)
    (hlim : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => dA.1 (c.2.1 y)) (𝓝[H] z) (𝓝 v))
    (hu : Tendsto (fun y => dA.1 (c.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (u : ℂ))) :
    ∃ δ : ℝ, 0 < δ ∧ Disjoint (ball ((u + A.shift : ℝ) : ℂ) δ)
      ((fun z => dA.1 z + (A.shift : ℂ)) '' (B.hull \ A.hull)) := by
  obtain ⟨δ, hδ, hside⟩ := exists_halfdisc_inv_mem_dom hc hdA hr hdom hlim hu
  refine ⟨δ, hδ, Set.disjoint_left.2 ?_⟩
  rintro w hwb ⟨z, hz, rfl⟩
  have hzA : z ∈ dA.dom := by
    change z ∈ (dA.dom : Set ℂ)
    rw [A.dom_eq]
    exact ⟨B.isHull.1 hz.1, hz.2⟩
  have hball : dA.1 z ∈ ball (u : ℂ) δ := by
    simpa only [ofReal_add, mem_ball, dist_add_right] using hwb
  have hzC := hside (dA.1 z) ⟨hdA.fwd_mem hzA, hball⟩
  rw [hdA.inv_fwd hzA] at hzC
  have hzB : z ∈ H \ B.hull := by
    rw [← B.dom_eq]
    exact hCB hzC
  exact hzB.2 hz.1

/-- A real incident interval supplies the zero own-prefix-minus-reference
lift limit. Only the component half-disc must lie in the own-prefix domain. -/
theorem tendsto_piece_lift_sub_of_realLimits {c dA dB : Chart}
    (hc : c.IsConformal) (A : HullModel dA) (B : HullModel dB)
    (hA : IsNormalized dA) (hB : IsNormalized dB) (hAB : A.hull ⊆ B.hull)
    (hCB : (c.dom : Set ℂ) ⊆ dB.dom) {x r u : ℝ} (hr : 0 < r)
    (hdom : ∀ z ∈ H ∩ ball (x : ℂ) r, c.2.1 z ∈ dA.dom)
    (hlim : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => dA.1 (c.2.1 y)) (𝓝[H] z) (𝓝 v))
    (hu : Tendsto (fun y => dA.1 (c.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (u : ℂ))) :
    Tendsto (fun z => dA.2.2 (c.2.1 z) - dB.2.2 (c.2.1 z))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨δ, hδ, hgap⟩ := exists_transition_gap_of_realLimits hc hA.conformal
    A B hCB hr hdom hlim hu
  refine tendsto_piece_lift_sub_comp A B hA hB hAB hδ hgap ?_ hu
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact hCB (hc.inv_mem_dom hz)

end InteractingSLE.Theorem14.WalkIntGerm
