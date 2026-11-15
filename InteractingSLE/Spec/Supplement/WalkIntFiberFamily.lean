/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFiberCollar

/-!
# Reference families from physical boundary landings

Real transition coordinates are constructed by the inverse fibre theorem.
The input records physical landings on retained hull boundaries instead.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFiber

open WalkIntCanon

/-- Nested retained charts with proper extensions and physical incident
intervals. No transition limit, lift comparison, or integer is supplied. -/
structure LandingHullFamily (c : Chart) where
  chart : ℕ → Chart
  normalized : ∀ i, IsNormalized (chart i)
  proper : ∀ i, GW1P.HasProperBdryExt (chart i)
  model : ∀ i, HullModel (chart i)
  interval : ℕ → Set ℝ
  anchor : ℝ
  dom_subset : ∀ i, (c.dom : Set ℂ) ⊆ (chart i).dom
  isOpen : ∀ i, IsOpen (interval i)
  isPreconnected : ∀ i, IsPreconnected (interval i)
  anchor_mem : ∀ i, anchor ∈ interval i
  landing : ∀ i x, x ∈ interval i → ∃ p : ℂ, p ∉ (chart i).dom ∧
    Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)
  base_subset : ∀ i, (model 0).hull ⊆ (model i).hull

/-- Every transition limit of the earlier incident family follows from
the physical landings and bounded proper inverse extensions. -/
def LandingHullFamily.incidentFamily {c : Chart} (F : LandingHullFamily c)
    (hc : c.IsConformal) : WalkIntGerm.IncidentHullFamily c where
  chart := F.chart
  normalized := F.normalized
  model := F.model
  interval := F.interval
  anchor := F.anchor
  dom_subset := F.dom_subset
  isOpen := F.isOpen
  isPreconnected := F.isPreconnected
  anchor_mem := F.anchor_mem
  base_subset := F.base_subset
  realLimits := by
    intro i x hx
    obtain ⟨p, hp, hland⟩ := F.landing i x hx
    exact exists_real_transition_limit_of_landing hc (F.normalized i).conformal
      (F.proper i) one_pos (fun z hz => F.dom_subset i (hc.inv_mem_dom hz.1)) hp hland

/-- A single integer works across all reference intervals. Real boundary
transition limits and reference agreement are conclusions of the proof. -/
theorem LandingHullFamily.exists_int {c : Chart} (F : LandingHullFamily c)
    (hc : c.IsConformal) (hL : c.HasDerivLift) :
    ∃ n : ℤ, ∀ i x, x ∈ F.interval i →
      Tendsto (fun y => (F.chart i).2.2 (c.2.1 y) - c.2.2 (c.2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n)) :=
  (F.incidentFamily hc).exists_int hc hL

end InteractingSLE.Theorem14.WalkIntFiber
