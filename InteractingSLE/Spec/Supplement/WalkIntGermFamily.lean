/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntGermGap

/-!
# Reference families need only their incident real intervals

The base boundary value is selected from the real-limit data, and all
anchor gaps follow from the reflected incident interval. Neither those
gaps nor any reference lift agreement is a field of this family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntGerm

open WalkIntCanon

/-- The remaining reference geometry: nested physical hulls and connected
incident intervals with real transition limits. -/
structure IncidentHullFamily (c : Chart) where
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

/-- The real base value and every transition-hull gap are consequences of
the incident interval data. -/
def IncidentHullFamily.retainedFamily {c : Chart} (F : IncidentHullFamily c)
    (hc : c.IsConformal) : RetainedHullFamily c := by
  let v : ℂ := (F.realLimits 0 F.anchor (F.anchor_mem 0)).choose
  have hv : v.im = 0 := (F.realLimits 0 F.anchor (F.anchor_mem 0)).choose_spec.1
  have ht : Tendsto (fun y => (F.chart 0).1 (c.2.1 y))
      (𝓝[H] (F.anchor : ℂ)) (𝓝 (v.re : ℂ)) := by
    have h := (F.realLimits 0 F.anchor (F.anchor_mem 0)).choose_spec.2
    change Tendsto (fun y => (F.chart 0).1 (c.2.1 y))
      (𝓝[H] (F.anchor : ℂ)) (𝓝 v) at h
    rwa [show v = (v.re : ℂ) from eq_ofReal_re_of_im_eq_zero hv] at h
  refine ⟨F.chart, F.normalized, F.model, F.interval, F.anchor, F.dom_subset,
    F.isOpen, F.isPreconnected, F.anchor_mem, F.realLimits, F.base_subset,
    v.re, ht, ?_⟩
  intro i
  obtain ⟨r, hr, hcover⟩ := Metric.isOpen_iff.1 (F.isOpen 0)
    F.anchor (F.anchor_mem 0)
  have hlim : ∀ z ∈ ball (F.anchor : ℂ) r, z.im = 0 →
      ∃ w : ℂ, w.im = 0 ∧ Tendsto (fun y => (F.chart 0).1 (c.2.1 y))
        (𝓝[H] z) (𝓝 w) := by
    intro z hz hz0
    have he : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
    rw [he, mem_ball, Sec7.Lemma71O.dist_ofReal_ofReal] at hz
    have h := F.realLimits 0 z.re (hcover hz)
    rwa [← he] at h
  exact exists_transition_gap_of_realLimits hc (F.normalized 0).conformal
    (F.model 0) (F.model i) (F.dom_subset i) hr
    (fun z hz => F.dom_subset 0 (hc.inv_mem_dom hz.1)) hlim ht

/-- The existing Bridge API receives a reference family with all anchor
lift comparisons proved from incident geometry. -/
def IncidentHullFamily.referenceFamily {c : Chart} (F : IncidentHullFamily c)
    (hc : c.IsConformal) : WalkIntBridge.ReferenceFamily c :=
  (F.retainedFamily hc).referenceFamily hc

/-- One integer works on all incident intervals, with no anchor-gap or
anchor-lift hypothesis. -/
theorem IncidentHullFamily.exists_int {c : Chart} (F : IncidentHullFamily c)
    (hc : c.IsConformal) (hL : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ F.interval i →
      Tendsto (fun y => (F.chart i).2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) :=
  (F.referenceFamily hc).exists_int hc hL

end InteractingSLE.Theorem14.WalkIntGerm
