/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun
import InteractingSLE.Spec.Supplement.WalkIntBridgeLift

/-!
# Reference families with geometric anchor data

The reference-family anchor agreement is now a conclusion of Aux. lemma 57.
The remaining input is a nested physical hull family whose transition hulls
miss the common incident anchor. No lift agreement is a field of this data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntCanon

/-- Geometric data for retained references. The base hull lies in every
reference hull, and each additional transition hull misses the base anchor.
Constructing these incident collars is still a planar geometry obligation. -/
structure RetainedHullFamily (c : Chart) where
  chart : ℕ → Chart
  normalized : ∀ i, IsNormalized (chart i)
  model : ∀ i, HullModel (chart i)
  interval : ℕ → Set ℝ
  anchor : ℝ
  dom_subset : ∀ i, (c.dom : Set ℂ) ⊆ (chart i).dom
  isOpen : ∀ i, IsOpen (interval i)
  isPreconnected : ∀ i, IsPreconnected (interval i)
  anchor_mem : ∀ i, anchor ∈ interval i
  realLimits : ∀ i x, x ∈ interval i → ∃ v : ℂ, v.im = 0 ∧
    Tendsto (fun y => (chart i).1 (c.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 v)
  base_subset : ∀ i, (model 0).hull ⊆ (model i).hull
  base_value : ℝ
  base_limit : Tendsto (fun y => (chart 0).1 (c.2.1 y))
    (𝓝[H] (anchor : ℂ)) (𝓝 (base_value : ℂ))
  anchor_gap : ∀ i, ∃ ρ : ℝ, 0 < ρ ∧
    Disjoint (ball ((base_value + (model 0).shift : ℝ) : ℂ) ρ)
      ((fun z => (chart 0).1 z + ((model 0).shift : ℂ)) ''
        ((model i).hull \ (model 0).hull))

/-- Convert physical retained hulls to the reference data used by the
existing common-integer theorem. In particular `anchor_agree` is proved. -/
def RetainedHullFamily.referenceFamily {c : Chart} (F : RetainedHullFamily c)
    (hc : c.IsConformal) : WalkIntBridge.ReferenceFamily c where
  chart := F.chart
  interval := F.interval
  anchor := F.anchor
  conformal := fun i => (F.normalized i).conformal
  hasDerivLift := fun i => (F.normalized i).derivLift
  dom_subset := F.dom_subset
  isOpen := F.isOpen
  isPreconnected := F.isPreconnected
  anchor_mem := F.anchor_mem
  realLimits := F.realLimits
  anchor_agree := by
    intro i
    obtain ⟨ρ, hρ, hgap⟩ := F.anchor_gap i
    have hphys : map c.2.1 (𝓝[H] (F.anchor : ℂ)) ≤ 𝓟 (H \ (F.model i).hull) := by
      refine le_principal_iff.2 ?_
      change ∀ᶠ z in 𝓝[H] (F.anchor : ℂ), c.2.1 z ∈ H \ (F.model i).hull
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [← (F.model i).dom_eq]
      exact F.dom_subset i (hc.inv_mem_dom hz)
    have hq : Tendsto (fun z => (F.chart 0).1 z + ((F.model 0).shift : ℂ))
        (map c.2.1 (𝓝[H] (F.anchor : ℂ)))
        (𝓝[H] ((F.base_value + (F.model 0).shift : ℝ) : ℂ)) := by
      apply tendsto_map'_iff.2
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa only [Function.comp_def, ofReal_add] using
          F.base_limit.add_const ((F.model 0).shift : ℂ)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        have hd := (F.normalized 0).conformal.fwd_mem
          (F.dom_subset 0 (hc.inv_mem_dom hz))
        simpa only [Function.comp_apply, QuantumZipper.H, mem_ofPred_eq,
          add_im, ofReal_im, add_zero] using hd
    have hlim := tendsto_lift_sub_of_nested (F.model 0) (F.model i)
      (F.normalized 0) (F.normalized i) (F.base_subset i) hphys hρ hgap hq
    simpa only [Function.comp_def] using tendsto_map'_iff.1 hlim

/-- The one integer follows from geometric hull gaps and connected incident
intervals; agreement of reference lifts is no longer an assumption. -/
theorem RetainedHullFamily.exists_int {c : Chart} (F : RetainedHullFamily c)
    (hc : c.IsConformal) (hL : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ F.interval i →
      Tendsto (fun y => (F.chart i).2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) :=
  (F.referenceFamily hc).exists_int hc hL

end InteractingSLE.Theorem14.WalkIntCanon
