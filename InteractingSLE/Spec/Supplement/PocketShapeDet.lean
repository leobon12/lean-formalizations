/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafShape
import InteractingSLE.Spec.Supplement.GB11ChartBdry

/-!
# Ordered contacts of shaped pockets

Packet PROVE-POCKETSHAPE. These deterministic consequences of an `IsPocketShape` reuse the
Janiszewski argument in `GB11ChartBdryPlanar`. In particular, a contact in the closure of a
shaped pocket is an endpoint; it cannot be strictly inside its right-wall parameter interval.
The existence of a shape is not assumed to have been proved by these lemmas.
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

/-- Absence of a common open subarc excludes every nontrivial common continuum. -/
theorem subsingleton_of_isPreconnected
    (hR : GB11.IsCompleteSimpleFlow αR)
    (hno : ∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL)
    {S : Set ℂ} (hS : S ⊆ range αR ∩ range αL) (hSc : IsPreconnected S) :
    S.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨a, b, hab, hsub⟩ := WalkCont.exists_Icc_image_subset_of_isPreconnected
    (isClosedEmbedding_of_isCompleteSimpleFlow hR).isEmbedding
    (fun z hz => (hS hz).1) hSc hx hy hxy
  exact hno a b hab (fun z hz => (hS (hsub hz)).2)

/-- The two upper parameters of a bounded shape are finite, and ordered on both walls. -/
theorem finite_parameters {C : Set ℂ} {s t : ℝ≥0} {u v : ℝ≥0∞}
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤) :
    v ≠ ⊤ ∧ s < u.toNNReal ∧ t < v.toNNReal := by
  have hv : v ≠ ⊤ := fun hv => hu (hs.top_iff.2 hv)
  have hsu : s < u.toNNReal := ENNReal.coe_lt_coe.1 (by
    rw [ENNReal.coe_toNNReal hu]
    exact hs.lt)
  exact ⟨hv, hsu, (hord s u.toNNReal t v.toNNReal hs.contact (hs.entry hu).1).1 hsu⟩

/-- A common point of the two shaped boundary intervals is an endpoint. -/
theorem contact_eq_endpoint
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v)
    {r q : ℝ≥0} (hr : s ≤ r) (hru : (r : ℝ≥0∞) ≤ u) (he : αR r = αL q) :
    r = s ∨ (r : ℝ≥0∞) = u := by
  obtain ⟨z, hz, -, -, hCz⟩ := id hC
  have hCo := GW4Reg.isOpen_of_mem_betweenComponents
    (GW4Reg.isClosed_range_of_isCompleteSimpleFlow hR)
    (GW4Reg.isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hCc : IsPreconnected C := hCz ▸ isPreconnected_connectedComponentIn
  have hzC : z ∈ C := hCz ▸ mem_connectedComponentIn hz
  have hsub : C ⊆ H \ (range αR ∪ range αL) := hCz ▸ connectedComponentIn_subset _ _
  have hCF : ∀ z ∈ C, z ∉ range αR ∪ range αL := fun z hz => (hsub hz).2
  rcases eq_or_lt_of_le hr with hrs | hrs
  · exact Or.inl hrs.symm
  have htq : t < q := (hord s r t q hs.contact he).1 hrs
  by_cases hu : u = ⊤
  · have hi := inter_subset_of_unboundedPocket hR hL hord hs.contact hCo hCc
      (fun z hz => (hsub hz).1) (hs.unbounded hu) hzC hCF hs.frontier_subset_Ici hs.mem_closure_exit
    have hh := hi ⟨⟨r, hr, rfl⟩, ⟨q, htq.le, he.symm⟩⟩
    exact (hrs.ne' (hR.2.1 (mem_singleton_iff.1 hh))).elim
  · obtain ⟨hv, -, -⟩ := finite_parameters hord hs hu
    have hru' : r ≤ u.toNNReal := by
      apply ENNReal.coe_le_coe.1
      rwa [ENNReal.coe_toNNReal hu]
    have hqv : q ≤ v.toNNReal := le_of_not_gt fun h =>
      (not_lt_of_ge hru') ((hord u.toNNReal r v.toNNReal q (hs.entry hu).1 he).2 h)
    have hfr : frontier C ⊆ αR '' Icc s u.toNNReal ∪ αL '' Icc t v.toNNReal := by
      refine hs.frontier_subset.trans (union_subset_union (image_mono ?_) (image_mono ?_))
      · intro r hr
        refine ⟨hr.1, ENNReal.coe_le_coe.1 ?_⟩
        simpa only [ENNReal.coe_toNNReal hu] using hr.2
      · intro q hq
        refine ⟨hq.1, ENNReal.coe_le_coe.1 ?_⟩
        simpa only [ENNReal.coe_toNNReal hv] using hq.2
    have hi := inter_subset_of_boundedPocket hR hL hord hs.contact (hs.entry hu).1 hCo hCc
      (hs.entry hu).2.2 hzC hCF hfr hs.mem_closure_exit (hs.entry hu).2.1
    rcases hi ⟨⟨r, ⟨hr, hru'⟩, rfl⟩, ⟨q, ⟨htq.le, hqv⟩, he.symm⟩⟩ with hh | hh
    · exact (hrs.ne' (hR.2.1 hh)).elim
    · right
      rw [hR.2.1 hh, ENNReal.coe_toNNReal hu]

/-- There is no common contact strictly inside a shaped right-wall interval. -/
theorem not_contact_of_mem_Ioo
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v)
    {r : ℝ≥0} (hsr : s < r) (hru : (r : ℝ≥0∞) < u) : αR r ∉ range αL := by
  rintro ⟨q, hq⟩
  rcases contact_eq_endpoint hR hL hord hC hs hsr.le hru.le hq.symm with h | h
  · exact hsr.ne' h
  · exact hru.ne h

end InteractingSLE.Theorem14.PocketShapeDet
