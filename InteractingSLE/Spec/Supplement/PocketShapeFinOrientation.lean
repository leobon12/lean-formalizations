/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeFinBounded

/-!
# Bounded chart orientation from positive boundary order

PROVE-POCKETSHAPE continuation. Strict order of positive boundary parameters rules out
the entry as the zero-limit. The order assertion is the explicit remaining winding/orientation
input, not a theorem proved by this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.PocketShapeFin

open GW4Reg PocketShapeDet

/-- A right-wall point in a bounded shaped pocket's closure is no later than the entry. -/
theorem right_parameter_le_entry
    {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤)
    {r : ℝ≥0} (hrC : αR r ∈ closure C) : r ≤ u.toNNReal := by
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hrfr : αR r ∈ frontier C := by
    rw [hCo.frontier_eq]
    exact ⟨hrC, fun hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).2 (Or.inl ⟨r, rfl⟩)⟩
  have hr : (r : ℝ≥0∞) ≤ u := by
    rcases hs.frontier_subset hrfr with ⟨r', hr', he⟩ | ⟨q, -, he⟩
    · exact hR.2.1 he ▸ hr'.2
    · exact (contact_bounds_of_mem_closure hR hL hord hC hs he.symm hrC).2
  apply ENNReal.coe_le_coe.1
  rwa [ENNReal.coe_toNNReal hu]

/-- Strict positive boundary order excludes the closing endpoint as the chart's zero-limit. -/
theorem not_tendsto_entry_of_positive_order
    {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤)
    {c : Chart} (hc : IsComponentChart (range αR) (range αL) C c)
    (hordB : ∀ (x y : ℝ) (r q : ℝ≥0), 0 < x → x < y →
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) →
      Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝 (αR q)) → r < q) :
    ¬ Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR u.toNNReal)) := by
  intro hentry
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hdi := GW3Word.differentiableOn_inv_of_isComponentChart hc hCo
  have hlim := hc.2.2.2.2.1
  let f : ℝ → ℂ := fun x => extendFrom H c.2.1 (x : ℂ)
  have hfc : Continuous f := GW3Word.continuous_extendFrom_ofReal hdi.continuousOn
    (fun x => (hlim x).imp fun p hp => hp.1)
  have hflim : ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (f x)) :=
    fun x => tendsto_extendFrom ((hlim x).imp fun p hp => hp.1)
  have hex : ∀ x : ℝ, 0 < x → ∃ r : ℝ≥0,
      Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) := by
    intro x hx
    obtain ⟨p, hp, hpR, -⟩ := hlim x
    obtain ⟨r, hr⟩ := hpR hx
    exact ⟨r, hr.symm ▸ hp⟩
  obtain ⟨r, hr⟩ := hex 1 zero_lt_one
  obtain ⟨q, hq⟩ := hex 2 (by norm_num)
  have hrq : r < q := hordB 1 2 r q zero_lt_one (by norm_num) hr hq
  have hqcl : αR q ∈ closure C := by
    have : (𝓝[H] (2 : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by norm_num)
    exact isClosed_closure.mem_of_tendsto hq
      (eventually_nhdsWithin_of_forall fun z hz => subset_closure (hc.2.2.1 hz))
  have hqu : q ≤ u.toNNReal := right_parameter_le_entry hR hL hord hC hs hu hqcl
  have hK : IsClosed (αR '' Icc 0 r) := (isCompact_Icc.image hR.1).isClosed
  have hfK : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x ∈ αR '' Icc 0 r := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))] with x hx hx1
    obtain ⟨r', hr'⟩ := hex x hx
    have hrr' : r' < r := hordB x 1 r' r hx hx1 hr' hr
    have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    have he : f x = αR r' := tendsto_nhds_unique (hflim x) hr'
    exact ⟨r', ⟨zero_le, hrr'.le⟩, he.symm⟩
  have hf0K : f 0 ∈ αR '' Icc 0 r :=
    hK.mem_of_tendsto (hfc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hfK
  have : (𝓝[H] (0 : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hf0 : f 0 = αR u.toNNReal :=
    tendsto_nhds_unique (by simpa only [Complex.ofReal_zero] using hflim 0) hentry
  obtain ⟨r', hr', he⟩ := hf0K
  have heu : r' = u.toNNReal := hR.2.1 (he.trans hf0)
  have hur : u.toNNReal ≤ r := heu ▸ hr'.2
  exact not_lt_of_ge (hqu.trans hur) hrq

/-- Outstanding local orientation input: positive boundary parameters increase along
the right wall of a bounded shaped component. This is not discharged here. -/
def BoundedPositiveBoundaryOrderStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    ∀ C ∈ betweenComponents (range αR) (range αL),
      ∀ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v → u ≠ ⊤ →
        ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
          ∀ (x y : ℝ) (r q : ℝ≥0), 0 < x → x < y →
            Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) →
            Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝 (αR q)) → r < q

/-- The remaining local boundary-order input implies the original bounded entry exclusion. -/
theorem boundedChartEntryExclusionStatement_of_positive_order
    (hB : BoundedPositiveBoundaryOrderStatement) : BoundedChartEntryExclusionStatement := by
  intro αR αL hR hL hord C hC s t u v hs hu c hc
  exact not_tendsto_entry_of_positive_order hR hL hord hC hs hu hc
    (hB αR αL hR hL hord C hC s t u v hs hu c hc)

end InteractingSLE.Theorem14.PocketShapeFin
