/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillRetained

/-!
# Remaining incident geometry for constructed retained prefix pairs

Hull models, raw fillings, nesting and normalization are already constructed.
The named remaining input supplies active-component containment, proper
joint inverse extensions, and consecutive physical incident intervals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFill

/-- The exact remaining local geometry for selected retained pairs. This
does not assert a proper boundary extension for arbitrary compact hulls. -/
structure RetainedBoundaryGeometry (c : Chart) (sR sL : ExplState) where
  pair : ℕ → RetainedPair sR sL
  proper : ∀ i, GW1P.HasProperBdryExt (pair i).chart
  active : ∀ i, (c.dom : Set ℂ) ⊆ H \ fillH (pair i).raw
  interval : ℕ → Set ℝ
  anchor : ℝ
  isOpen : ∀ i, IsOpen (interval i)
  isPreconnected : ∀ i, IsPreconnected (interval i)
  anchor_mem : ∀ i, anchor ∈ interval i
  landing : ∀ i x, x ∈ interval i → ∃ p : ℂ,
    (p ∈ closure (pair i).raw ∨ p.im = 0) ∧
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)
  base_raw : ∀ i, (pair 0).raw ⊆ (pair i).raw

/-- Construct the preceding reference-family API from certified prefix
pairs and the explicitly remaining physical boundary geometry. -/
def RetainedBoundaryGeometry.landingFamily {c : Chart} {sR sL : ExplState}
    (G : RetainedBoundaryGeometry c sR sL) : WalkIntFiber.LandingHullFamily c where
  chart := fun i => (G.pair i).chart
  normalized := fun i => (G.pair i).normalized
  proper := G.proper
  model := fun i => (G.pair i).model
  interval := G.interval
  anchor := G.anchor
  dom_subset := by
    intro i z hz
    rw [(G.pair i).model.dom_eq, (G.pair i).filled]
    exact G.active i hz
  isOpen := G.isOpen
  isPreconnected := G.isPreconnected
  anchor_mem := G.anchor_mem
  landing := by
    intro i x hx
    obtain ⟨p, hp, hlim⟩ := G.landing i x hx
    refine ⟨p, ?_, hlim⟩
    intro hpd
    have hH := (G.pair i).normalized.conformal.dom_subset hpd
    rcases hp with hp | hp
    · have hpf : p ∈ fillH (G.pair i).raw := mem_fillH_of_mem_closure hH hp
      have hnot : p ∉ (G.pair i).model.hull := by
        change p ∈ ((G.pair i).chart.dom : Set ℂ) at hpd
        rw [(G.pair i).model.dom_eq] at hpd
        exact hpd.2
      exact hnot ((G.pair i).filled.symm ▸ hpf)
    · exact (ne_of_gt (show 0 < p.im from hH)) hp
  base_subset := by
    intro i
    rw [(G.pair 0).filled, (G.pair i).filled]
    exact fillH_mono (G.base_raw i)

/-- The same integer serves all retained prefix pairs and incident points.
The family input supplies physical incidence, not any integer or lift limit. -/
theorem RetainedBoundaryGeometry.exists_int {c : Chart} {sR sL : ExplState}
    (G : RetainedBoundaryGeometry c sR sL) (hc : c.IsConformal) (hL : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ G.interval i →
      Tendsto (fun y => (G.pair i).chart.2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) :=
  G.landingFamily.exists_int hc hL

/-- A real match using any constructed retained pair has the inherited
zero lift from its raw physical collar and the remaining active inclusion. -/
theorem RetainedBoundaryGeometry.isRealMatchRef {c : Chart} {sR sL : ExplState}
    (G : RetainedBoundaryGeometry c sR sL) (hc : c.IsConformal) (i : ℕ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {x bx a r : ℝ}
    (ha : a ∉ (jumps : Set ℝ)) (hr : 0 < r)
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ)))
    (hgap : Disjoint (ball (a : ℂ) r) (WalkBdry.wsetOf sR ∪ WalkBdry.wsetOf sL))
    (hbx : bx = b a) :
    WalkIntBridge.IsRealMatchRef sR sL b jumps c (G.pair i).chart x bx :=
  WalkIntGerm.isRealMatchRef_of_incident hc (G.pair i).normalized
    (G.landingFamily.dom_subset i)
    ((G.pair i).isRealIncidentMatch ha hr hland hgap hbx)

end InteractingSLE.Theorem14.WalkIntFill
