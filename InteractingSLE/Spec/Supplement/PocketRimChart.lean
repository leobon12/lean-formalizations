/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketRimLocal
import InteractingSLE.Spec.Supplement.GW3LawChart

/-!
# Comparison of charts on a bounded shaped pocket

PROVE-POCKETSHAPE continuation. Restrict chart-boundary walls to the component
closure. Their common contacts are just the two shape endpoints, so the existing
dilation-uniqueness theorem applies without global absence of common arcs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Function
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.PocketRim

open GW4Reg

/-- Boundary walls of a component chart may be restricted to the component closure. -/
theorem isComponentChart_inter_closure {R L C : Set ℂ} {c : Chart}
    (hc : IsComponentChart R L C c) :
    IsComponentChart (R ∩ closure C) (L ∩ closure C) C c := by
  obtain ⟨hd, hmF, hmI, hinv, hlim, hlift, hderiv⟩ := hc
  refine ⟨hd, hmF, hmI, hinv, fun x => ?_, hlift, hderiv⟩
  obtain ⟨p, hp, hpR, hpL⟩ := hlim x
  have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hpC : p ∈ closure C := isClosed_closure.mem_of_tendsto hp
    (eventually_nhdsWithin_of_forall fun z hz => subset_closure (hmI hz))
  exact ⟨p, hp, fun hx => ⟨hpR hx, hpC⟩, fun hx => ⟨hpL hx, hpC⟩⟩

/-- Common boundary continua in the closure of a bounded shape are trivial. -/
theorem subsingleton_common_closure_of_bounded_shape {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤)
    {S : Set ℂ} (hS : S ⊆ (range αR ∩ closure C) ∩ (range αL ∩ closure C))
    (hSc : IsPreconnected S) : S.Subsingleton := by
  have hsub : S ⊆ {αR s, αR u.toNNReal} := by
    intro p hp
    obtain ⟨⟨⟨r, hr⟩, hrC⟩, ⟨⟨q, hq⟩, -⟩⟩ := hS hp
    have he : αR r = αL q := hr.trans hq.symm
    have hcl : αR r ∈ closure C := hr.symm ▸ hrC
    rcases PocketShapeDet.contact_in_closure_eq_endpoint hR hL hord hC hs he hcl with he | he
    · exact Or.inl (hr.symm.trans (congrArg αR he))
    · have her : r = u.toNNReal := by
        apply ENNReal.coe_injective
        simpa only [ENNReal.coe_toNNReal hu] using he
      exact Or.inr (hr.symm.trans (congrArg αR her))
  exact hSc.isDiscrete_iff_subsingleton.1
    (((finite_singleton (αR u.toNNReal)).insert (αR s)).subset hsub).isDiscrete

/-- Charts of a bounded shaped pocket are related by a positive dilation.
Only the shape's local contact restriction is used; global common arcs are allowed. -/
theorem exists_dilation_of_bounded_shape_charts {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤)
    {c d : Chart} (hc : IsComponentChart (range αR) (range αL) C c)
    (hd : IsComponentChart (range αR) (range αL) C d) :
    ∃ a : ℝ, 0 < a ∧ ∀ w ∈ H, d.1 (c.2.1 w) = (a : ℂ) * w := by
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  exact GW3Law.exists_dilation_of_isComponentChart (isComponentChart_inter_closure hc)
    (isComponentChart_inter_closure hd) hCo
    (fun S hS hSc => subsingleton_common_closure_of_bounded_shape hR hL hord hC hs hu hS hSc)

/-- Positive boundary order for one chart transfers to every chart on the same bounded shape. -/
theorem positive_boundary_order_of_bounded_shape_chart {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤)
    {c d : Chart} (hc : IsComponentChart (range αR) (range αL) C c)
    (hd : IsComponentChart (range αR) (range αL) C d)
    (horder : ∀ (x y : ℝ) (r q : ℝ≥0), 0 < x → x < y →
      Tendsto d.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) →
      Tendsto d.2.1 (𝓝[H] (y : ℂ)) (𝓝 (αR q)) → r < q) :
    ∀ (x y : ℝ) (r q : ℝ≥0), 0 < x → x < y →
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) →
      Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝 (αR q)) → r < q := by
  obtain ⟨a, ha, hscale⟩ := exists_dilation_of_bounded_shape_charts hR hL hord hC hs hu hd hc
  have hcomp : ∀ w ∈ H, d.2.1 w = c.2.1 (QuantumZipper.CA.realMobius a 0 0 1 w) := by
    intro w hw
    calc
      d.2.1 w = c.2.1 (c.1 (d.2.1 w)) := (hc.2.2.2.1.1 (hd.2.2.1 hw)).symm
      _ = c.2.1 ((a : ℂ) * w) := congrArg c.2.1 (hscale w hw)
      _ = _ := by simp only [QuantumZipper.CA.realMobius, Complex.ofReal_zero,
        Complex.ofReal_one, zero_mul, add_zero, zero_add, div_one]
  have hlim : ∀ (x : ℝ) (p : ℂ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) →
      Tendsto d.2.1 (𝓝[H] ((x / a : ℝ) : ℂ)) (𝓝 p) := by
    intro x p hp
    apply GW3Law.tendsto_comp_realMobius (by simpa only [mul_one, mul_zero, sub_zero] using ha)
      hcomp (by simp) (x := x / a)
    simpa only [mul_div_cancel₀ _ ha.ne', add_zero, zero_mul, zero_add, div_one] using hp
  intro x y r q hx hxy hr hq
  exact horder (x / a) (y / a) r q (div_pos hx ha) ((div_lt_div_iff_of_pos_right ha).2 hxy)
    (hlim x _ hr) (hlim y _ hq)

end InteractingSLE.Theorem14.PocketRim
