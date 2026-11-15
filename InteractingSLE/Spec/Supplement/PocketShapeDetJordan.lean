/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeDet

/-!
# The Jordan boundary determined by a pocket shape

Packet PROVE-POCKETSHAPE. A bounded shape determines its entire Jordan boundary. An
unbounded shape has the same property after `GB11Chart.mu`, which sends infinity to zero.
These statements do not need a component chart or its as-yet-unidentified limit at zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric.JordanMap (IsJordanCurve)

namespace InteractingSLE.Theorem14.PocketShapeDet

open GW4Reg GB11Chart

/-- Two bounded components of the complement of a Jordan curve coincide. -/
theorem eq_of_bounded_jordan_components {J C D : Set ℂ} (hJ : IsJordanCurve J)
    (hCo : IsOpen C) (hCc : IsConnected C) (hCb : IsBounded C)
    (hCJ : Disjoint C J) (hCfr : frontier C ⊆ J)
    (hDo : IsOpen D) (hDc : IsConnected D) (hDb : IsBounded D)
    (hDJ : Disjoint D J) (hDfr : frontier D ⊆ J) : C = D := by
  obtain ⟨p, hp⟩ := hCc.nonempty
  obtain ⟨q, hq⟩ := hDc.nonempty
  have hCp := eq_connectedComponentIn_of_frontier_subset hCo hCc.isPreconnected hp
    (fun z hz => disjoint_left.1 hCJ hz) hCfr
  have hDq := eq_connectedComponentIn_of_frontier_subset hDo hDc.isPreconnected hq
    (fun z hz => disjoint_left.1 hDJ hz) hDfr
  obtain ⟨a, ha, b, -, -, hb, -, hsplit, -, -⟩ :=
    Foundations.Jordan.jordan_curve_components_complex hJ
  have hc : C = connectedComponentIn Jᶜ a := by
    have hpJ : p ∈ Jᶜ := disjoint_left.1 hCJ hp
    rw [hsplit] at hpJ
    rcases hpJ with hpJ | hpJ
    · exact hCp.symm.trans (connectedComponentIn_eq hpJ).symm
    · exact (hb ((connectedComponentIn_eq hpJ) ▸ (hCp ▸ hCb))).elim
  have hd : D = connectedComponentIn Jᶜ a := by
    have hqJ : q ∈ Jᶜ := disjoint_left.1 hDJ hq
    rw [hsplit] at hqJ
    rcases hqJ with hqJ | hqJ
    · exact hDq.symm.trans (connectedComponentIn_eq hqJ).symm
    · exact (hb ((connectedComponentIn_eq hqJ) ▸ (hDq ▸ hDb))).elim
  exact hc.trans hd.symm

variable {αR αL : ℝ≥0 → ℂ}

/-- A bounded shape's two full wall intervals form a Jordan curve. -/
theorem isJordanCurve_of_bounded_shape
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤) :
    IsJordanCurve (αR '' Icc s u.toNNReal ∪ αL '' Icc t v.toNNReal) := by
  obtain ⟨hv, hsu, htv⟩ := finite_parameters hord hs hu
  obtain ⟨f, hfc, hfi, hf0, hf1, hfim⟩ := exists_unitParam hR.1 hR.2.1 hsu
  obtain ⟨g, hgc, hgi, hg0, hg1, hgim⟩ := exists_unitParam hL.1 hL.2.1 htv
  rw [← hfim, ← hgim]
  refine Sec7.isJordanCurve_image_union hfc hgc hfi hgi
    (by rw [hf0, hg0]; exact hs.contact) (by rw [hf1, hg1]; exact (hs.entry hu).1) ?_
  rw [hfim, hgim, hf0, hf1]
  rintro z ⟨⟨r, hr, rfl⟩, ⟨q, -, hq⟩⟩
  have hru : (r : ℝ≥0∞) ≤ u := by
    rw [← ENNReal.coe_toNNReal hu]
    exact ENNReal.coe_le_coe.2 hr.2
  rcases contact_eq_endpoint hR hL hord hC hs hr.1 hru hq.symm with he | he
  · exact Or.inl (congrArg αR he)
  · right
    have : r = u.toNNReal := by
      apply ENNReal.coe_injective
      rwa [ENNReal.coe_toNNReal hu]
    exact this ▸ mem_singleton _

/-- The full boundary of a bounded shaped pocket, without a chart-endpoint hypothesis. -/
theorem frontier_eq_of_bounded_shape
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u ≠ ⊤) :
    frontier C = αR '' Icc s u.toNNReal ∪ αL '' Icc t v.toNNReal := by
  have hJ := isJordanCurve_of_bounded_shape hR hL hord hC hs hu
  obtain ⟨hv, -, -⟩ := finite_parameters hord hs hu
  obtain ⟨z, hz, -, -, hCz⟩ := id hC
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hCc : IsPreconnected C := hCz ▸ isPreconnected_connectedComponentIn
  have hzC : z ∈ C := hCz ▸ mem_connectedComponentIn hz
  have hsub : C ⊆ H \ (range αR ∪ range αL) := hCz ▸ connectedComponentIn_subset _ _
  have hCF : ∀ z ∈ C, z ∉ αR '' Icc s u.toNNReal ∪ αL '' Icc t v.toNNReal :=
    fun z hz h => (hsub hz).2 ((union_subset_union (image_subset_range _ _) (image_subset_range _ _)) h)
  have hfr : frontier C ⊆ αR '' Icc s u.toNNReal ∪ αL '' Icc t v.toNNReal := by
    refine hs.frontier_subset.trans (union_subset_union (image_mono ?_) (image_mono ?_))
    · intro r hr
      refine ⟨hr.1, ENNReal.coe_le_coe.1 ?_⟩
      simpa only [ENNReal.coe_toNNReal hu] using hr.2
    · intro q hq
      refine ⟨hq.1, ENNReal.coe_le_coe.1 ?_⟩
      simpa only [ENNReal.coe_toNNReal hv] using hq.2
  have heq := eq_connectedComponentIn_of_frontier_subset hCo hCc hzC hCF hfr
  have hsplit := Foundations.Schoenflies.jordan_split hJ (hCF z hzC)
    (heq ▸ (hs.entry hu).2.2)
  rw [heq] at hsplit
  exact hsplit.1

/-- The two compactified tails of an unbounded shape form a Jordan curve. -/
theorem isJordanCurve_of_unbounded_shape
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u = ⊤) :
    IsJordanCurve (mu '' (αR '' Ici s ∪ αL '' Ici t) ∪ {0}) := by
  obtain ⟨f, hfc, hfi, hf0, hf1, hfim⟩ := exists_muArm hR s
  obtain ⟨g, hgc, hgi, hg0, hg1, hgim⟩ := exists_muArm hL t
  have heq : f '' Icc 0 1 ∪ g '' Icc 0 1 = mu '' (αR '' Ici s ∪ αL '' Ici t) ∪ {0} := by
    rw [hfim, hgim, image_union]
    ext z
    simp only [mem_union]
    tauto
  rw [← heq]
  refine Sec7.isJordanCurve_image_union hfc hgc hfi hgi
    (by rw [hf0, hg0, hs.contact]) (by rw [hf1, hg1]) ?_
  rw [hfim, hgim, hf0, hf1]
  rintro z ⟨hz | hz, hz' | hz'⟩
  · obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hz
    obtain ⟨_, ⟨q, -, rfl⟩, hq⟩ := hz'
    have hh := contact_eq_endpoint hR hL hord hC hs hr (hu ▸ le_top) (mu_injective hq).symm
    rcases hh with he | he
    · exact Or.inl (congrArg (fun r => mu (αR r)) he)
    · exact (ENNReal.coe_ne_top (he.trans hu)).elim
  · exact Or.inr hz'
  · exact Or.inr hz
  · exact Or.inr hz

/-- The compactified domain of any between-component is a bounded open connected set. -/
theorem mu_component_props
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) :
    IsOpen (mu '' C) ∧ IsConnected (mu '' C) ∧ IsBounded (mu '' C) := by
  obtain ⟨z, hz, -, -, hCz⟩ := id hC
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hCc : IsConnected C := hCz ▸ isConnected_connectedComponentIn_iff.2 hz
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  have hCHb : C ⊆ Hbar := fun z hz => mem_Hbar_of_mem_H (hCH hz)
  refine ⟨isOpen_mu_image hCo hCH, hCc.image _ (continuousOn_mu_Hbar.mono hCHb), ?_⟩
  refine (isBounded_closedBall (x := (0 : ℂ)) (r := 1)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  exact mem_closedBall_zero_iff.2 (norm_mu_le_one (hCHb hz))

/-- A compactified shaped pocket is disjoint from its two compactified wall tails. -/
theorem disjoint_mu_tails {C : Set ℂ}
    (hC : C ∈ betweenComponents (range αR) (range αL)) (s t : ℝ≥0) :
    Disjoint (mu '' C) (mu '' (αR '' Ici s ∪ αL '' Ici t) ∪ {0}) := by
  rw [disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ (⟨w, hw, he⟩ | he)
  · have hz' := Sec7.Prop74B.subset_of_mem_betweenComponents hC hz
    exact hz'.2 ((union_subset_union (image_subset_range _ _) (image_subset_range _ _)) (mu_injective he ▸ hw))
  · exact mu_ne_zero_of_mem_Hbar
      (mem_Hbar_of_mem_H (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1) he

/-- Compactification preserves the frontier containment needed for the Jordan theorem. -/
theorem frontier_mu_subset_tails
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) :
    frontier (mu '' C) ⊆ mu '' (αR '' Ici s ∪ αL '' Ici t) ∪ {0} := by
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  exact (frontier_mu_image_subset hCo hCH).trans
    (union_subset_union (image_mono hs.frontier_subset_Ici) le_rfl)

/-- The full Jordan boundary of an unbounded shaped pocket after compactification. -/
theorem frontier_mu_eq_of_unbounded_shape
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) (hu : u = ⊤) :
    frontier (mu '' C) = mu '' (αR '' Ici s ∪ αL '' Ici t) ∪ {0} := by
  have hJ := isJordanCurve_of_unbounded_shape hR hL hord hC hs hu
  obtain ⟨hCo, hCc, hCb⟩ := mu_component_props hR hL hC
  obtain ⟨z, hz⟩ := hCc.nonempty
  have hdis := disjoint_mu_tails hC s t
  have heq := eq_connectedComponentIn_of_frontier_subset hCo hCc.isPreconnected hz
    (fun w hw => disjoint_left.1 hdis hw) (frontier_mu_subset_tails hR hL hC hs)
  have hsplit := Foundations.Schoenflies.jordan_split hJ (disjoint_left.1 hdis hz) (heq ▸ hCb)
  rw [heq] at hsplit
  exact hsplit.1

/-- Two shapes starting at the same right-wall time have the same upper right-wall time. -/
theorem upper_le_of_same_exit
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C D : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t t' : ℝ≥0} {u v u' v' : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s t u v) (hs' : IsPocketShape αR αL D s t' u' v') : u ≤ u' := by
  by_contra hn
  have hlt : u' < u := lt_of_not_ge hn
  have hu' : u' ≠ ⊤ := ne_top_of_lt hlt
  have hsu' : s < u'.toNNReal := ENNReal.coe_lt_coe.1 (by
    rw [ENNReal.coe_toNNReal hu']
    exact hs'.lt)
  have hru : (u'.toNNReal : ℝ≥0∞) < u := by
    rwa [ENNReal.coe_toNNReal hu']
  exact not_contact_of_mem_Ioo hR hL hord hC hs hsu' hru
    ⟨v'.toNNReal, (hs'.entry hu').1.symm⟩

/-- The exit determines the shaped component, including the unbounded case. -/
theorem eq_of_same_exit
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C D : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    (hD : D ∈ betweenComponents (range αR) (range αL))
    {s t t' : ℝ≥0} {u v u' v' : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s t u v) (hs' : IsPocketShape αR αL D s t' u' v') : C = D := by
  have huu' := le_antisymm (upper_le_of_same_exit hR hL hord hC hs hs')
    (upper_le_of_same_exit hR hL hord hD hs' hs)
  subst u'
  have htt' : t = t' := hL.2.1 (hs.contact.symm.trans hs'.contact)
  subst t'
  by_cases hu : u = ⊤
  · have hJ := isJordanCurve_of_unbounded_shape hR hL hord hC hs hu
    obtain ⟨hCo, hCc, hCb⟩ := mu_component_props hR hL hC
    obtain ⟨hDo, hDc, hDb⟩ := mu_component_props hR hL hD
    have he := eq_of_bounded_jordan_components hJ hCo hCc hCb (disjoint_mu_tails hC s t)
      (frontier_mu_subset_tails hR hL hC hs) hDo hDc hDb (disjoint_mu_tails hD s t)
      (frontier_mu_subset_tails hR hL hD hs')
    exact (Set.image_injective.mpr mu_injective) he
  · have hv := (finite_parameters hord hs hu).1
    have hv' := (finite_parameters hord hs' hu).1
    have hvv' : v = v' := by
      have he : v.toNNReal = v'.toNNReal :=
        hL.2.1 ((hs.entry hu).1.symm.trans (hs'.entry hu).1)
      rw [← ENNReal.coe_toNNReal hv, ← ENNReal.coe_toNNReal hv', he]
    subst v'
    have hJ := isJordanCurve_of_bounded_shape hR hL hord hC hs hu
    have hfrC := frontier_eq_of_bounded_shape hR hL hord hC hs hu
    have hfrD := frontier_eq_of_bounded_shape hR hL hord hD hs' hu
    have hCo := isOpen_of_mem_betweenComponents
      (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
    have hDo := isOpen_of_mem_betweenComponents
      (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hD
    obtain ⟨z, hz, -, -, hCz⟩ := id hC
    obtain ⟨w, hw, -, -, hDw⟩ := id hD
    have hCc : IsConnected C := hCz ▸ isConnected_connectedComponentIn_iff.2 hz
    have hDc : IsConnected D := hDw ▸ isConnected_connectedComponentIn_iff.2 hw
    apply eq_of_bounded_jordan_components hJ hCo hCc (hs.entry hu).2.2
      (hfrC ▸ disjoint_left.2 (fun z hz hfr => (hCo.frontier_eq ▸ hfr).2 hz)) hfrC.subset hDo hDc (hs'.entry hu).2.2
      (hfrD ▸ disjoint_left.2 (fun z hz hfr => (hDo.frontier_eq ▸ hfr).2 hz)) hfrD.subset

/-- Distinct shaped pockets have non-overlapping right-wall parameter intervals. -/
theorem nonoverlap
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C D : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    (hD : D ∈ betweenComponents (range αR) (range αL)) (hne : C ≠ D)
    {s t s' t' : ℝ≥0} {u v u' v' : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s t u v) (hs' : IsPocketShape αR αL D s' t' u' v') :
    u' ≤ (s : ℝ≥0∞) ∨ u ≤ (s' : ℝ≥0∞) := by
  rcases lt_trichotomy s s' with hlt | he | hlt
  · right
    by_contra hn
    exact not_contact_of_mem_Ioo hR hL hord hC hs hlt (lt_of_not_ge hn)
      ⟨t', hs'.contact.symm⟩
  · subst s'
    exact (hne (eq_of_same_exit hR hL hord hC hD hs hs')).elim
  · left
    by_contra hn
    exact not_contact_of_mem_Ioo hR hL hord hD hs' hlt (lt_of_not_ge hn)
      ⟨t, hs.contact.symm⟩

end InteractingSLE.Theorem14.PocketShapeDet
