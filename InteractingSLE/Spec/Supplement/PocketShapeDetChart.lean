/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeDetJordan

/-!
# Locating the boundary value of a component chart

Packet PROVE-POCKETSHAPE. The limit at zero is a common contact in the closure of
the component. For a shaped pocket it is therefore an endpoint. In the unbounded
case it is necessarily the exit; only the bounded case has a second finite endpoint.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.PocketShapeDet

open GW4Reg GB11Chart

variable {αR αL : ℝ≥0 → ℂ}

/-- The boundary value at zero belongs to both closed walls. -/
theorem chart_zero_mem_inter {R L C : Set ℂ} (hRc : IsClosed R) (hLc : IsClosed L)
    (hCo : IsOpen C) {c : Chart} (hc : IsComponentChart R L C c)
    {p : ℂ} (hp : Tendsto c.2.1 (𝓝[H] 0) (𝓝 p)) : p ∈ R ∩ L := by
  have hd := GW3Word.differentiableOn_inv_of_isComponentChart hc hCo
  have hlim := hc.2.2.2.2.1
  let q : ℝ → ℂ := fun x => extendFrom H c.2.1 (x : ℂ)
  have hqc : Continuous q := GW3Word.continuous_extendFrom_ofReal hd.continuousOn
    (fun x => (hlim x).imp fun p hp => hp.1)
  have hqlim : ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (q x)) :=
    fun x => tendsto_extendFrom ((hlim x).imp fun p hp => hp.1)
  have hside : ∀ x : ℝ, (0 < x → q x ∈ R) ∧ (x < 0 → q x ∈ L) := by
    intro x
    have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    obtain ⟨p, hp, hpR, hpL⟩ := hlim x
    have he := tendsto_nhds_unique (hqlim x) hp
    exact ⟨fun hx => he.symm ▸ hpR hx, fun hx => he.symm ▸ hpL hx⟩
  have : (𝓝[H] (0 : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hq0 : q 0 = p := tendsto_nhds_unique (by simpa only [Complex.ofReal_zero] using hqlim 0) hp
  rw [← hq0]
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), q x ∈ R :=
    eventually_nhdsWithin_of_forall fun x hx => (hside x).1 hx
  have hneg : ∀ᶠ x in 𝓝[<] (0 : ℝ), q x ∈ L :=
    eventually_nhdsWithin_of_forall fun x hx => (hside x).2 hx
  exact ⟨hRc.mem_of_tendsto (hqc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hpos,
    hLc.mem_of_tendsto (hqc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hneg⟩

/-- A component chart's boundary limit lies in the closure of its component. -/
theorem chart_zero_mem_closure {R L C : Set ℂ} {c : Chart}
    (hc : IsComponentChart R L C c) {p : ℂ}
    (hp : Tendsto c.2.1 (𝓝[H] 0) (𝓝 p)) : p ∈ closure C := by
  have : (𝓝[H] (0 : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  exact isClosed_closure.mem_of_tendsto hp
    (eventually_nhdsWithin_of_forall fun z hz => subset_closure (hc.2.2.1 hz))

/-- A common contact in the closure of a shaped pocket lies within its right-wall interval. -/
theorem contact_bounds_of_mem_closure
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v)
    {r q : ℝ≥0} (he : αR r = αL q) (hrC : αR r ∈ closure C) :
    s ≤ r ∧ (r : ℝ≥0∞) ≤ u := by
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hfr : αR r ∈ frontier C := by
    rw [hCo.frontier_eq]
    exact ⟨hrC, fun hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).2 (Or.inl ⟨r, rfl⟩)⟩
  rcases hs.frontier_subset hfr with ⟨r', hr', hrr'⟩ | ⟨q', hq', hqq'⟩
  · exact hR.2.1 hrr' ▸ hr'
  · have hqq : q' = q := hL.2.1 (hqq'.trans he)
    subst q'
    have hsr : s ≤ r := le_of_not_gt fun h =>
      (not_lt_of_ge hq'.1) ((hord r s q t he hs.contact).1 h)
    refine ⟨hsr, ?_⟩
    by_cases hu : u = ⊤
    · rw [hu]; exact le_top
    · have hv := (finite_parameters hord hs hu).1
      have hqv : q ≤ v.toNNReal := ENNReal.coe_le_coe.1 (by
        simpa only [ENNReal.coe_toNNReal hv] using hq'.2)
      have hru : r ≤ u.toNNReal := le_of_not_gt fun h =>
        (not_lt_of_ge hqv) ((hord u.toNNReal r v.toNNReal q (hs.entry hu).1 he).1 h)
      rw [← ENNReal.coe_toNNReal hu]
      exact ENNReal.coe_le_coe.2 hru

/-- A common contact in a shaped pocket's closure is its exit or its finite entry. -/
theorem contact_in_closure_eq_endpoint
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v)
    {r q : ℝ≥0} (he : αR r = αL q) (hrC : αR r ∈ closure C) :
    r = s ∨ (r : ℝ≥0∞) = u := by
  obtain ⟨hr, hru⟩ := contact_bounds_of_mem_closure hR hL hord hC hs he hrC
  exact contact_eq_endpoint hR hL hord hC hs hr hru he

/-- A component chart can tend only to the exit or to the finite entry of a shaped pocket. -/
theorem chart_zero_eq_endpoint
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v)
    {c : Chart} (hc : IsComponentChart (range αR) (range αL) C c)
    {p : ℂ} (hp : Tendsto c.2.1 (𝓝[H] 0) (𝓝 p)) :
    p = αR s ∨ (u ≠ ⊤ ∧ p = αR u.toNNReal) := by
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  obtain ⟨⟨r, hr⟩, ⟨q, hq⟩⟩ := chart_zero_mem_inter
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hCo hc hp
  have he := contact_in_closure_eq_endpoint hR hL hord hC hs (hr.trans hq.symm)
    (hr.symm ▸ chart_zero_mem_closure hc hp)
  rcases he with he | he
  · exact Or.inl (hr.symm.trans (congrArg αR he))
  · right
    have hu : u ≠ ⊤ := he ▸ ENNReal.coe_ne_top
    refine ⟨hu, hr.symm.trans (congrArg αR ?_)⟩
    apply ENNReal.coe_injective
    rwa [ENNReal.coe_toNNReal hu]

/-- The chart's limit at zero is the exit of an unbounded shaped pocket. -/
theorem chart_zero_eq_exit_of_unbounded
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u = ⊤)
    {c : Chart} (hc : IsComponentChart (range αR) (range αL) C c)
    {p : ℂ} (hp : Tendsto c.2.1 (𝓝[H] 0) (𝓝 p)) : p = αR s := by
  rcases chart_zero_eq_endpoint hR hL hord hC hs hc hp with he | ⟨hn, -⟩
  · exact he
  · exact (hn hu).elim

end InteractingSLE.Theorem14.PocketShapeDet
