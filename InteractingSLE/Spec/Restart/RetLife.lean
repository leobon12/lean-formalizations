/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76Exit
import InteractingSLE.Spec.Supplement.G7RetainedChart

/-!
# The retained continuation stopped at its first contact with the boundary (ruling R55)

Packet PROVE-RETAUX79C. The specification's continuation in the proof of Lemma 7.6 (p. 268: "a simple interior curve
until its first new contact with `∂D`") stops at its first contact with `η₁[0, u] ∪ η₂[0, r] ∪ ℝ`. This file gives the
deterministic facts about that stop:

* **`contStop_shorten`**, `contLife_shorten`, `canonRetPath_shorten`, `canonRetLife_shorten`: stopping at the first
  contact with `K ∪ L` is stopping at the first contact with `K` for the path with lifetime shortened to that stop. So
  every landed result about the canonical retained clock (stop set = retained set) applies to the new lifetime;
* `isPathGood_mono`: a good path stays good with a shorter lifetime;
* **`lt_contStop_union_realLine`**: the new stop is strictly after the start when the tip is interior;
* `le_contStop_union_realLine`: a path that stays in the joint unbounded domain up to `e` stops at or after `e`;
* **`isDisjointPair_of_avoid`** (the planar-topology lemma): a second path that avoids `K ∪ ℝ` on `(r, r']`,
  `K = α[0, a] ∪ β[0, r]`, keeps `(a, r')` a disjoint pair: both tips stay adherent to the new joint unbounded domain
  (the slit `β[r, r']` meets `K ∪ ℝ` only at `β(r)`, and an arc does not separate the plane; for the new second tip,
  Janiszewski's theorem for the disjoint compacts `α[0, a]` and `β[0, r']`);
* `isDisjointPair_of_lt_contStop`: hence `(a, r')` is a disjoint pair for every `r < r' < contStop`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7 Sec7

/-! ### Shortening the lifetime -/

section Shorten

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {K L : Set ℂ}

/-- **Stopping at the first contact with `K ∪ L` is stopping at the first contact with `K` with the lifetime shortened
to that stop.** -/
theorem contStop_shorten : contStop η (contStop η ζ a (K ∪ L)) a K = contStop η ζ a (K ∪ L) := by
  refine le_antisymm contStop_le (iSup₂_le fun t ht => le_contStop ?_)
  exact ⟨ht.1, le_contStop ht, fun t' h1 h2 hK => ht.2.2 t' h1 h2 (Or.inl hK)⟩

theorem contLife_shorten : contLife η (contStop η ζ a (K ∪ L)) a K = contLife η ζ a (K ∪ L) := by
  unfold contLife
  rw [contStop_shorten]

theorem canonRetPath_shorten (D : Set ℂ) (φ : ℂ → ℂ) (c : ℝ) :
    canonRetPath D φ η (contStop η ζ a (K ∪ L)) a K c = canonRetPath D φ η ζ a (K ∪ L) c := by
  funext u
  unfold canonRetPath
  rw [contLife_shorten]

theorem canonRetLife_shorten (D : Set ℂ) (φ : ℂ → ℂ) (c : ℝ) :
    canonRetLife D φ η (contStop η ζ a (K ∪ L)) a K c = canonRetLife D φ η ζ a (K ∪ L) c := by
  unfold canonRetLife
  rw [contLife_shorten]

/-- If the path avoids `L` just after `a` and the first contact with `K` is after `a`, so is the first contact with
`K ∪ L`. -/
theorem lt_contStop_union (hK : (a : ℝ≥0∞) < contStop η ζ a K) (hL : ∀ᶠ t in 𝓝[>] a, η t ∉ L) :
    (a : ℝ≥0∞) < contStop η ζ a (K ∪ L) := by
  obtain ⟨t₁, ht₁, hat₁⟩ := lt_biSup_iff.1 hK
  have hat₁' : a < t₁ := ENNReal.coe_lt_coe.1 hat₁
  obtain ⟨u, hau, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hL
  set t₀ := min t₁ u with ht₀
  have hat₀ : a < t₀ := lt_min hat₁' hau
  refine (ENNReal.coe_lt_coe.2 hat₀).trans_le (le_contStop ⟨hat₀.le,
    (ENNReal.coe_le_coe.2 (min_le_left _ _)).trans ht₁.2.1, fun t' h1 h2 => ?_⟩)
  rintro (h | h)
  · exact ht₁.2.2 t' h1 (h2.trans_le (min_le_left _ _)) h
  · exact hu ⟨h1, h2.trans_le (min_le_right _ _)⟩ h

/-- A time `e ≤ ζ` before which the path avoids `K ∪ L` after `a` is at most the stop. -/
theorem le_contStop_of_avoid {e : ℝ≥0} (hae : a ≤ e) (he : (e : ℝ≥0∞) ≤ ζ)
    (hav : ∀ t, a < t → t < e → η t ∉ K ∪ L) : (e : ℝ≥0∞) ≤ contStop η ζ a (K ∪ L) :=
  le_contStop ⟨hae, he, hav⟩

end Shorten

/-! ### Good paths with a shorter lifetime -/

section Good

variable {η : ℝ≥0 → ℂ} {ζ ζ' : ℝ≥0∞} {x : ℝ}

/-- A good path stays good with a shorter lifetime. -/
theorem isPathGood_mono (hp : IsPathGood η ζ x) (h : ζ' ≤ ζ) : IsPathGood η ζ' x := by
  obtain ⟨hi, w, hw, hw0, hg⟩ := hp
  refine ⟨hi.mono fun t ht => (show (t : ℝ≥0∞) ≤ ζ' from ht).trans h, w,
    hw.mono fun t ht => (show (t : ℝ≥0∞) < ζ' from ht).trans_le h, hw0, ?_⟩
  exact ⟨hg.1, hg.2.1.mono fun t ht => (show (t : ℝ≥0∞) ≤ ζ' from ht).trans h,
    fun t ht => hg.2.2 t (ht.trans_le h)⟩

/-- A good path is continuous at every time before its lifetime. -/
theorem isPathGood_continuousAt (hp : IsPathGood η ζ x) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : ContinuousAt η t := by
  refine (hp.continuousOn t ht.le).continuousAt ?_
  by_cases hζ : ζ = ⊤
  · rw [hζ]
    exact Filter.univ_mem' fun s => show (s : ℝ≥0∞) ≤ ⊤ from le_top
  · have hlt : t < ζ.toNNReal := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hζ]; exact ht
    refine Filter.mem_of_superset (Iio_mem_nhds hlt) fun s hs => ?_
    show (s : ℝ≥0∞) ≤ ζ
    rw [← ENNReal.coe_toNNReal hζ]
    exact ENNReal.coe_le_coe.2 (le_of_lt hs)

/-- Just after an interior time before the lifetime, a good path is off the real line. -/
theorem isPathGood_eventually_notMem_realLine (hp : IsPathGood η ζ x) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hH : η t ∈ H) : ∀ᶠ s in 𝓝[>] t, η s ∉ realLine := by
  have h1 : ∀ᶠ s in 𝓝 t, η s ∈ H :=
    (isPathGood_continuousAt hp ht).eventually (QuantumZipper.isOpen_H.mem_nhds hH)
  filter_upwards [nhdsWithin_le_nhds h1] with s hs hR
  exact (ne_of_gt (show (0 : ℝ) < (η s).im from hs)) hR

/-- **The first contact with `O ∪ η[0, a] ∪ ℝ` is strictly after `a`** for a retained continuation. -/
theorem lt_contStop_union_realLine {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ}
    (hR : IsRetCont η ζ x a O φ ψ) : (a : ℝ≥0∞) < contStop η ζ a (O ∪ η '' Icc 0 a ∪ realLine) :=
  lt_contStop_union hR.lt_contStop (isPathGood_eventually_notMem_realLine hR.path hR.lt hR.tipH)

/-- **The retained continuation with the boundary stop is a retained continuation for the shortened lifetime.** -/
theorem isRetCont_shorten {a : ℝ≥0} {O : Set ℂ} {φ ψ : ℂ → ℂ} (hR : IsRetCont η ζ x a O φ ψ) :
    IsRetCont η (contStop η ζ a (O ∪ η '' Icc 0 a ∪ realLine)) x a O φ ψ :=
  { hR with
    path := isPathGood_mono hR.path contStop_le
    lt := lt_contStop_union_realLine hR }

end Good

/-! ### The planar-topology lemma: later pairs are disjoint pairs -/

section Planar

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a r r' : ℝ≥0}

/-- A point of the closure of a set `S` lying in an open set `U` is in the closure of `S ∩ U`. -/
theorem mem_closure_inter_of_isOpen {S U : Set ℂ} {z : ℂ} (hz : z ∈ closure S) (hU : IsOpen U) (hzU : z ∈ U) :
    z ∈ closure (S ∩ U) := by
  have h := hU.inter_closure ⟨hzU, hz⟩
  rw [inter_comm] at h
  exact h

/-- **The planar-topology lemma** (ruling R55): if `(a, r)` is a disjoint pair and the second path avoids
`α[0, a] ∪ β[0, r] ∪ ℝ` on `(r, r']`, `r' < ζ₂`, then `(a, r')` is a disjoint pair. -/
theorem isDisjointPair_of_avoid (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ r) (hrr' : r < r') (hr' : (r' : ℝ≥0∞) < ζ₂)
    (hav : ∀ s, r < s → s ≤ r' → β s ∉ α '' Icc 0 a ∪ β '' Icc 0 r ∪ realLine) :
    Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ r' := by
  obtain ⟨haζ, hrζ, hβr, hdisj, hclβ, hclα⟩ := hpair
  set K₀ := α '' Icc 0 a ∪ β '' Icc 0 r with hK₀
  set K := α '' Icc 0 a ∪ β '' Icc 0 r' with hK
  set G := β '' Icc r r' with hG
  have haζ' : (a : ℝ≥0∞) ≤ ζ₁ := haζ.le
  have hr'ζ : (r' : ℝ≥0∞) ≤ ζ₂ := hr'.le
  have hrζ' : (r : ℝ≥0∞) ≤ ζ₂ := hrζ.le
  have hαc : IsCompact (α '' Icc 0 a) := IsPathGood.isCompact_image_Icc hp₁ haζ'
  have hβc : IsCompact (β '' Icc 0 r') := IsPathGood.isCompact_image_Icc hp₂ hr'ζ
  have hK₀c : IsCompact K₀ := hαc.union (IsPathGood.isCompact_image_Icc hp₂ hrζ')
  have hKc : IsCompact K := hαc.union hβc
  have hGc : IsCompact G := IsPathGood.isCompact_image_Icc hp₂ hr'ζ
  -- points of the slit after `β(r)` are in `ℍ` and off `K₀`
  have hslitH : ∀ s, r < s → s ≤ r' → β s ∈ H ∧ β s ∉ K₀ := by
    intro s h1 h2
    have hs := hav s h1 h2
    refine ⟨?_, fun h => hs (Or.inl h)⟩
    have h0 : 0 ≤ (β s).im := IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 h2).trans hr'ζ)
    exact lt_of_le_of_ne h0 fun h => hs (Or.inr h.symm)
  have hsplit : β '' Icc 0 r' = β '' Icc 0 r ∪ G := by
    rw [hG, ← image_union, Icc_union_Icc_eq_Icc zero_le hrr'.le]
  have hdisj' : Disjoint (α '' Icc 0 a) (β '' Icc 0 r') := by
    rw [hsplit, Set.disjoint_union_right]
    refine ⟨hdisj, Set.disjoint_left.2 ?_⟩
    rintro _ hα ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · exact Set.disjoint_left.1 hdisj hα ⟨r, ⟨zero_le, le_rfl⟩, by rw [h]⟩
    · exact (hslitH s h hs.2).2 (Or.inl hα)
  have hact : activeDomain α a β r' = H \ fillH K := Lemma76Exit.unboundedPart_eq hKc.isClosed
  have hact₀ : activeDomain α a β r = H \ fillH K₀ := Lemma76Exit.unboundedPart_eq hK₀c.isClosed
  -- the slit: points of the old domain off `G` are in the new domain
  obtain ⟨R, hR0, hRb⟩ := (hK₀c.union hGc).isBounded.subset_ball_lt 0 0
  have hGint : (K₀ ∪ HalfPlaneSep.lowerDisc R) ∩ G = {β r} := by
    ext z
    constructor
    · rintro ⟨hz, ⟨s, hs, rfl⟩⟩
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h]; exact mem_singleton _
      · exfalso
        obtain ⟨hsH, hsK⟩ := hslitH s h hs.2
        rcases hz with hz | hz
        · exact hsK hz
        · exact HalfPlaneSep.notMem_lowerDisc_of_mem_H hsH hz
    · rintro rfl
      exact ⟨Or.inl (Or.inr ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩), ⟨r, ⟨le_rfl, hrr'.le⟩, rfl⟩⟩
  have hKsub : K ⊆ K₀ ∪ G := by
    rintro z (hz | hz)
    · exact Or.inl (Or.inl hz)
    · rw [hsplit] at hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
  have hβc' : ContinuousOn β (Icc r r') := hp₂.continuousOn.mono fun s hs =>
    (show (s : ℝ≥0∞) ≤ ζ₂ from (ENNReal.coe_le_coe.2 hs.2).trans hr'ζ)
  have hβi' : InjOn β (Icc r r') := hp₂.1.mono fun s hs =>
    (show (s : ℝ≥0∞) ≤ ζ₂ from (ENNReal.coe_le_coe.2 hs.2).trans hr'ζ)
  have hslit : ∀ z ∈ H \ fillH K₀, z ∉ G → z ∈ H \ fillH K := by
    intro z hz hzG
    have h1 := mem_H_diff_fillH_union_of_mem_jordanOut hK₀c hGc hR0 (subset_union_left.trans hRb)
      (subset_union_right.trans hRb) (by rw [hGint]; exact isPreconnected_singleton) hz
      (Lemma76Exit.compl_image_Icc_subset_jordanOut hrr' hβc' hβi' hzG)
    exact ⟨h1.1, fun h => h1.2 (fillH_mono hKsub h)⟩
  -- the first tip: the slit avoids it
  have hαG : α a ∉ G := by
    rintro ⟨s, hs, hsa⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · exact Set.disjoint_left.1 hdisj ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩ ⟨r, ⟨zero_le, le_rfl⟩, by rw [h, hsa]⟩
    · exact (hslitH s h hs.2).2 (Or.inl ⟨a, ⟨zero_le, le_rfl⟩, hsa.symm⟩)
  have hclα' : α a ∈ closure (H \ fillH K) := by
    rw [hact₀] at hclα
    refine closure_mono ?_ (mem_closure_inter_of_isOpen hclα hGc.isClosed.isOpen_compl hαG)
    exact fun z hz => hslit z hz.1 hz.2
  -- the second tip: free for the first prefix along the second path, then Janiszewski
  have hfree : ∀ s ∈ Icc 0 r', HalfPlaneSep.IsFreeAt (α '' Icc 0 a) (β s) := by
    have hX : IsPreconnected (β '' Icc 0 r') :=
      isPreconnected_Icc.image _ (IsPathGood.continuousOn_Icc hp₂ hr'ζ)
    have hXF : β '' Icc 0 r' ⊆ {w | 0 ≤ w.im} \ α '' Icc 0 a := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 hs.2).trans hr'ζ),
        fun h => Set.disjoint_left.1 hdisj' h ⟨s, hs, rfl⟩⟩
    rcases HalfPlaneSep.isFreeAt_or_isTrappedAt_of_isPreconnected hαc.isClosed hX hXF with h | h
    · exact fun s hs => h _ ⟨s, hs, rfl⟩
    · exfalso
      obtain ⟨ε, hε, hdis⟩ := h (β r) ⟨r, ⟨zero_le, hrr'.le⟩, rfl⟩
      rw [hact₀] at hclβ
      obtain ⟨z, hz, hzr⟩ := Metric.mem_closure_iff.1 hclβ ε hε
      refine Set.disjoint_left.1 hdis (show z ∈ ball (β r) ε by rw [mem_ball, dist_comm]; exact hzr) ?_
      exact ⟨hz.1, fun h => hz.2 (fillH_mono subset_union_left h)⟩
  have hclβ' : β r' ∈ closure (H \ fillH K) := by
    have h2 := HalfPlaneSep.mem_closure_inter_of_isFreeAt (Lemma76Exit.tip_mem_closure hp₂ hr') (fun _ h => h.1)
      (hfree r' ⟨zero_le, le_rfl⟩)
    refine closure_mono ?_ h2
    rintro z ⟨hz1, hz2⟩
    have h3 := HalfPlaneSep.H_diff_fillH_inter_subset hαc hβc
      (fun w hw => (Set.disjoint_left.1 hdisj' hw.1 hw.2).elim) ⟨hz2, hz1⟩
    exact h3
  have hβr' : β r' ∈ H := (hslitH r' hrr' le_rfl).1
  exact ⟨haζ, hr', hβr', hdisj', by rw [hact]; exact hclβ', by rw [hact]; exact hclα'⟩

/-- **Later pairs before the boundary stop are disjoint pairs** (ruling R55): for `r < r'` before the first contact
of the second path with `α[0, a] ∪ β[0, r] ∪ ℝ`, `(a, r')` is a disjoint pair. -/
theorem isDisjointPair_of_lt_contStop (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂)
    (hpair : Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ r) (hrr' : r < r')
    (hr' : (r' : ℝ≥0∞) < contStop β ζ₂ r (α '' Icc 0 a ∪ β '' Icc 0 r ∪ realLine)) :
    Lemma76Exit.IsDisjointPair α ζ₁ a β ζ₂ r' := by
  refine isDisjointPair_of_avoid hp₁ hp₂ hpair hrr' (hr'.trans_le contStop_le) fun s h1 h2 => ?_
  rcases eq_or_lt_of_le h2 with h | h
  · rw [h]
    exact notMem_of_lt_contStop hrr' hr'
  · exact notMem_of_lt_contStop h1 ((ENNReal.coe_lt_coe.2 h).trans hr')

end Planar

end Restart.RetAux79

end InteractingSLE
