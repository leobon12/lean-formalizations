/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntGermFamily

/-!
# Raw real collars and their filled hulls

A half-ball missing the raw set belongs to one complementary component.
If an active chart approaches its real center from outside the filling,
the whole half-ball is outside the filling. This proves the physical real
gap needed by the inherited zero-lift theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntGerm

/-- A preconnected subset of the raw complement stays outside the filling
if any one of its points is outside the filling. -/
theorem subset_H_diff_fillH_of_mem {Γ S : Set ℂ}
    (hS : IsPreconnected S) (hSΓ : S ⊆ H \ closure Γ) {p : ℂ}
    (hp : p ∈ S) (hpF : p ∈ H \ fillH Γ) : S ⊆ H \ fillH Γ := by
  have hcomp := hS.subset_connectedComponentIn hp hSΓ
  have hnb : ¬ Bornology.IsBounded (connectedComponentIn (H \ closure Γ) p) := by
    intro hb
    exact hpF.2 ⟨hpF.1, Or.inr hb⟩
  intro z hz
  refine ⟨(hSΓ hz).1, ?_⟩
  rintro ⟨-, hcl | hb⟩
  · exact (hSΓ hz).2 hcl
  · apply hnb
    rw [connectedComponentIn_eq (hcomp hz)]
    exact hb

/-- A raw gap about a real point is also a filled-hull gap once the upper
half-ball meets the active complement. -/
theorem disjoint_ball_fillH_of_mem {Γ : Set ℂ} {a r : ℝ}
    (hgap : Disjoint (ball (a : ℂ) r) Γ) {p : ℂ}
    (hpb : p ∈ ball (a : ℂ) r) (hpF : p ∈ H \ fillH Γ) :
    Disjoint (ball (a : ℂ) r) (fillH Γ) := by
  have hcl := hgap.closure_right isOpen_ball
  have hconn : IsPreconnected (H ∩ ball (a : ℂ) r) :=
    ((convex_halfSpace_im_gt 0).inter (convex_ball _ _)).isPreconnected
  have hsub : H ∩ ball (a : ℂ) r ⊆ H \ closure Γ := fun z hz =>
    ⟨hz.1, fun he => Set.disjoint_left.1 hcl hz.2 he⟩
  have hout := subset_H_diff_fillH_of_mem hconn hsub ⟨hpF.1, hpb⟩ hpF
  exact Set.disjoint_left.2 fun z hzb hzF => (hout ⟨hzF.1, hzb⟩).2 hzF

/-- Landing from an active component supplies the point of the raw gap
that is outside the filling. -/
theorem disjoint_ball_fillH_of_landing {c : Chart} (hc : c.IsConformal)
    {Γ : Set ℂ} (hC : (c.dom : Set ℂ) ⊆ H \ fillH Γ) {x a r : ℝ}
    (hr : 0 < r) (hgap : Disjoint (ball (a : ℂ) r) Γ)
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ))) :
    Disjoint (ball (a : ℂ) r) (fillH Γ) := by
  let _ : NeBot (𝓝[H] (x : ℂ)) := Sec7.Lemma71O.nhdsWithin_H_ofReal_neBot x
  have hb : ∀ᶠ z in 𝓝[H] (x : ℂ), c.2.1 z ∈ ball (a : ℂ) r :=
    hland (ball_mem_nhds (a : ℂ) hr)
  have hboth : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H ∧ c.2.1 z ∈ ball (a : ℂ) r := by
    filter_upwards [self_mem_nhdsWithin, hb] with z hz hzb
    exact ⟨hz, hzb⟩
  obtain ⟨z, hzH, hzb⟩ := hboth.exists
  exact disjoint_ball_fillH_of_mem hgap hzb (hC (hc.inv_mem_dom hzH))

/-- A surviving raw real collar has zero inherited lift. The active-domain
containment, rather than raw separation alone, excludes filled pockets. -/
theorem tendsto_lift_zero_comp_of_raw_gap {c d : Chart} (hc : c.IsConformal)
    (M : WalkIntCanon.HullModel d) (hd : WalkIntCanon.IsNormalized d)
    {Γ : Set ℂ} (hM : M.hull = fillH Γ) (hC : (c.dom : Set ℂ) ⊆ d.dom)
    {x a r : ℝ} (hr : 0 < r) (hgap : Disjoint (ball (a : ℂ) r) Γ)
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ))) :
    Tendsto (fun z => d.2.2 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hCF : (c.dom : Set ℂ) ⊆ H \ fillH Γ := by
    rw [← hM, ← M.dom_eq]
    exact hC
  have hfilled := disjoint_ball_fillH_of_landing hc hCF hr hgap hland
  rw [← hM] at hfilled
  exact WalkIntCanon.tendsto_lift_zero_comp hc M hd hr hfilled hland

end InteractingSLE.Theorem14.WalkIntGerm
