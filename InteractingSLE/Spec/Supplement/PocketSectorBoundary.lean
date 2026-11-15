/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketSectorChart

/-!
# Non-contact boundary points of an oriented component chart

PROVE-POCKETSHAPE continuation. No common subarc and boundary nonconstancy imply
that every positive boundary interval has a limit on the right wall off the left
wall. In particular, an oriented between-component has a frontier point on just
the right wall. Real connectors are allowed throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.PocketSector

open GW4Reg

/-- Every positive interval has a right-wall boundary limit that is not on the left wall. -/
theorem exists_boundary_limit_off_left {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR)
    (hno : ∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL)
    {C : Set ℂ} (hCo : IsOpen C) {c : Chart}
    (hc : IsComponentChart (range αR) (range αL) C c)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ x ∈ Ioo a b, ∃ r : ℝ≥0,
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) ∧ αR r ∉ range αL := by
  have hdi := GW3Word.differentiableOn_inv_of_isComponentChart hc hCo
  have hlim := hc.2.2.2.2.1
  let f : ℝ → ℂ := fun x => extendFrom H c.2.1 (x : ℂ)
  have hfc : Continuous f := GW3Word.continuous_extendFrom_ofReal hdi.continuousOn
    (fun x => (hlim x).imp fun p hp => hp.1)
  have hflim : ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (f x)) :=
    fun x => tendsto_extendFrom ((hlim x).imp fun p hp => hp.1)
  have hfR : ∀ x ∈ Ioo a b, f x ∈ range αR := by
    intro x hx
    obtain ⟨p, hp, hpR, -⟩ := hlim x
    have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    exact tendsto_nhds_unique (hflim x) hp ▸ hpR (ha.trans_lt hx.1)
  have hex : ∃ x ∈ Ioo a b, f x ∉ range αL := by
    by_contra hn
    push Not at hn
    have hsub : f '' Ioo a b ⊆ range αR ∩ range αL := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hfR x hx, hn x hx⟩
    have hsingle := PocketShapeDet.subsingleton_of_isPreconnected hR hno hsub
      (isPreconnected_Ioo.image f hfc.continuousOn)
    obtain ⟨m, hm⟩ := nonempty_Ioo.2 hab
    have hconst : ∀ x ∈ Ioo a b, f x = f m := fun x hx =>
      hsingle ⟨x, hx, rfl⟩ ⟨m, hm, rfl⟩
    have hinj : InjOn c.2.1 H := by
      intro x hx y hy he
      rw [← hc.2.2.2.1.2 hx, he, hc.2.2.2.1.2 hy]
    exact GW3Word.false_of_tendsto_const hdi hinj hab
      (fun x hx => hconst x hx ▸ hflim x)
  obtain ⟨x, hx, hxL⟩ := hex
  obtain ⟨r, hr⟩ := hfR x hx
  exact ⟨x, hx, r, hr.symm ▸ hflim x, hr.symm ▸ hxL⟩

/-- An oriented between-component has a frontier point on the right wall off the left wall. -/
theorem exists_right_wall_frontier_off_left {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hno : ∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    (hU : GW3.HasOrientedUniformizer (range αR) (range αL) C) :
    ∃ r : ℝ≥0, αR r ∈ frontier C ∧ αR r ∉ range αL := by
  obtain ⟨c, hc⟩ := GW3.exists_isComponentChart_of_hasOrientedUniformizer hU
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  obtain ⟨x, -, r, hr, hrL⟩ := exists_boundary_limit_off_left hR hno hCo hc
    (a := 0) (b := 1) le_rfl zero_lt_one
  have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  refine ⟨r, ?_, hrL⟩
  rw [hCo.frontier_eq]
  refine ⟨isClosed_closure.mem_of_tendsto hr
    (eventually_nhdsWithin_of_forall fun z hz => subset_closure (hc.2.2.1 hz)), ?_⟩
  exact fun h => (Sec7.Prop74B.subset_of_mem_betweenComponents hC h).2 (Or.inl ⟨r, rfl⟩)

end InteractingSLE.Theorem14.PocketSector
