/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCoherence

/-!
# Retained-prefix reference families and their common integer

Continuation of PROVE-T14-WALKINT. A reference is allowed to cover only a
connected interval of the component boundary. Agreement of the inherited
reference lifts at one common anchor makes all the interval integers equal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntBridge

/-- A continuous derivative argument of a conformal chart comes from an
analytic derivative logarithm. -/
theorem hasDerivLift_of_continuous_arg {c : Chart} (hc : c.IsConformal)
    (hθ : ContinuousOn c.2.2 c.dom)
    (harg : ∀ z ∈ (c.dom : Set ℂ), deriv c.1 z =
      (‖deriv c.1 z‖ : ℂ) * exp ((c.2.2 z : ℂ) * I)) : c.HasDerivLift := by
  have hne : ∀ z ∈ (c.dom : Set ℂ), deriv c.1 z ≠ 0 := by
    intro z hz
    have h := Sec7.Lemma71O.deriv_fwd_mul_deriv_inv hc (hc.fwd_mem hz)
    rw [hc.inv_fwd hz] at h
    intro he
    rw [he, zero_mul] at h
    exact zero_ne_one h
  have hd := hc.differentiableOn_fwd.deriv c.dom.isOpen
  let L : ℂ → ℂ := fun z => (Real.log ‖deriv c.1 z‖ : ℂ) + (c.2.2 z : ℂ) * I
  have hLc : ContinuousOn L c.dom :=
    (Complex.continuous_ofReal.comp_continuousOn
      (hd.continuousOn.norm.log fun z hz => norm_ne_zero_iff.2 (hne z hz))).add
      ((Complex.continuous_ofReal.comp_continuousOn hθ).mul continuousOn_const)
  have he : ∀ z ∈ (c.dom : Set ℂ), exp (L z) = deriv c.1 z := by
    intro z hz
    dsimp only [L]
    rw [exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.2 (hne z hz))]
    exact (harg z hz).symm
  refine ⟨L, ⟨differentiableOn_of_continuousOn_of_exp_eq c.dom.isOpen hLc hd he, he⟩,
    fun z _ => ?_⟩
  simp only [L, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
    mul_one, mul_zero, add_zero, zero_add]

/-- Retained-prefix charts for one component, together with their connected
incident intervals and a shared normalization anchor. The intervals need not
be bounded uniformly, and no individual reference must cover all matches. -/
structure ReferenceFamily (c : Chart) where
  chart : ℕ → Chart
  interval : ℕ → Set ℝ
  anchor : ℝ
  conformal : ∀ i, (chart i).IsConformal
  hasDerivLift : ∀ i, (chart i).HasDerivLift
  dom_subset : ∀ i, (c.dom : Set ℂ) ⊆ (chart i).dom
  isOpen : ∀ i, IsOpen (interval i)
  isPreconnected : ∀ i, IsPreconnected (interval i)
  anchor_mem : ∀ i, anchor ∈ interval i
  realLimits : ∀ i x, x ∈ interval i → ∃ v : ℂ, v.im = 0 ∧
    Tendsto (fun y => (chart i).1 (c.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 v)
  anchor_agree : ∀ i,
    Tendsto (fun y => (chart i).2.2 (c.2.1 y) - (chart 0).2.2 (c.2.1 y))
      (𝓝[H] (anchor : ℂ)) (𝓝 0)

/-- All reference charts have the same boundary integer relative to the
component chart. -/
theorem ReferenceFamily.exists_int {c : Chart} (F : ReferenceFamily c)
    (hc : c.IsConformal) (hL : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ F.interval i →
      Tendsto (fun y => (F.chart i).2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) := by
  have hex : ∀ i, ∃ n : ℤ, ∀ x ∈ F.interval i,
      Tendsto (fun y => (F.chart i).2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) := fun i =>
    WalkInt.exists_int_tendsto_lift_sub_on hc (F.conformal i) hL
      (F.hasDerivLift i) (F.dom_subset i) (F.isOpen i) (F.isPreconnected i)
      (F.realLimits i)
  choose n hn using hex
  have hsame : ∀ i, n i = n 0 := by
    intro i
    have := Sec7.Lemma71O.nhdsWithin_H_ofReal_neBot F.anchor
    have h := (F.anchor_agree i).add (hn 0 F.anchor (F.anchor_mem 0))
    rw [zero_add] at h
    have h' : Tendsto
        (fun y => (F.chart i).2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (F.anchor : ℂ)) (𝓝 (2 * π * n 0)) := by
      refine h.congr fun y => ?_
      ring
    have he := tendsto_nhds_unique (hn i F.anchor (F.anchor_mem i)) h'
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast mul_left_cancel₀ hpi he
  exact ⟨n 0, fun i x hx => hsame i ▸ hn i x hx⟩

end InteractingSLE.Theorem14.WalkIntBridge
