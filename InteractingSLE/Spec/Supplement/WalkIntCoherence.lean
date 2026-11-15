/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormLift
import InteractingSLE.Spec.Sec7.Lemma71OArc

/-!
# One transition integer on a connected boundary interval

Packet PROVE-T14-WALKINT. This is the connected-interval part of GW3's
normalization argument (specification p. 636), for a fixed reference chart.
The local Schwarz-reflection integer comes from `Lemma71O`; its propagation
uses `Lemma71O.eq_of_isPreconnected_of_local` directly.

This result requires the component domain to lie in the reference domain.
Constructing that reference from the retained walk prefixes, and identifying
its inherited lift with each piece lift, are separate geometric obligations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkInt

/-- A transition with real boundary limits on a connected open real interval
has one lift-difference integer on the entire interval, when the first chart's
domain is contained in the second chart's domain. -/
theorem exists_int_tendsto_lift_sub_on {c₁ c₂ : Chart}
    (hc₁ : c₁.IsConformal) (hc₂ : c₂.IsConformal)
    (hL₁ : c₁.HasDerivLift) (hL₂ : c₂.HasDerivLift)
    (hdom : (c₁.dom : Set ℂ) ⊆ c₂.dom)
    {J : Set ℝ} (hJo : IsOpen J) (hJc : IsPreconnected J)
    (hlim : ∀ x ∈ J, ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => c₂.1 (c₁.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 v)) :
    ∃ n : ℤ, ∀ x ∈ J,
      Tendsto (fun y => c₂.2.2 (c₁.2.1 y) - c₁.2.2 (c₁.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) := by
  obtain ⟨L₁, hL₁d, hL₁i⟩ := hL₁
  obtain ⟨L₂, hL₂d, hL₂i⟩ := hL₂
  let P : ℝ → ℤ → Prop := fun x n =>
    Tendsto (fun y => (L₂ (c₁.2.1 y) - L₁ (c₁.2.1 y)).im)
      (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n))
  have huniq : ∀ x ∈ J, ∀ m m' : ℤ, P x m → P x m' → m = m' := by
    intro x _ m m' hm hm'
    have := Sec7.Lemma71O.nhdsWithin_H_ofReal_neBot x
    have he := tendsto_nhds_unique hm hm'
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast mul_left_cancel₀ hpi he
  have hlocal : ∀ x ∈ J, ∃ m : ℤ, ∃ ε > 0,
      ∀ y ∈ J, |y - x| < ε → P y m := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hJo x hx
    have hlim' : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
        Tendsto (fun y => c₂.1 (c₁.2.1 y)) (𝓝[H] z) (𝓝 v) := by
      intro z hz hz0
      have he : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
      rw [he, mem_ball, Sec7.Lemma71O.dist_ofReal_ofReal] at hz
      have h := hlim z.re (hball hz)
      rwa [← he] at h
    obtain ⟨m, ε, hε, _, hm⟩ := Sec7.Lemma71O.exists_int_tendsto_of_realLimits
      hc₁ rfl hL₁d c₂.dom.isOpen hdom hc₂.differentiableOn_fwd
      (fun z hz w hw he => by
        rw [← hc₂.inv_fwd hz, ← hc₂.inv_fwd hw]
        exact congrArg c₂.2.1 he)
      (fun z hz => hc₂.fwd_mem hz) hL₂d hr hlim'
    refine ⟨m, ε, hε, fun y _ hy => ?_⟩
    apply hm (y : ℂ) _ (Complex.ofReal_im y)
    rwa [mem_ball, Sec7.Lemma71O.dist_ofReal_ofReal, Real.dist_eq]
  rcases J.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun _ hx => hx.elim⟩
  obtain ⟨m, ε, hε, hm⟩ := hlocal x₀ hx₀
  have hm₀ : P x₀ m := hm x₀ hx₀ (by simpa only [sub_self, abs_zero] using hε)
  refine ⟨m, fun x hx => ?_⟩
  have h := Sec7.Lemma71O.eq_of_isPreconnected_of_local
    hJc huniq hlocal hx₀ hx hm₀
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Complex.sub_im, ← hL₂i _ (hdom (hc₁.inv_mem_dom hy)),
    ← hL₁i _ (hc₁.inv_mem_dom hy)]

end InteractingSLE.Theorem14.WalkInt
