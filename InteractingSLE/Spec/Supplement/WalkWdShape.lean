/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketMirrorAssembly
import InteractingSLE.Spec.Supplement.PocketCompassOrientation
import InteractingSLE.Spec.Supplement.GB11ChartBdry

/-!
# The landings of a component chart avoid the other wall; the closing contact of a bounded pocket

Packet PROVE-WALK-WORDS2 (`hMatch` of Theorem 1.4's walk leaf: finiteness of the exceptional coordinates, and the
exit data `BeforeExit` of bounded components). Deterministic. For two complete simple flows `α`, `β` with the
contact order and the pocket shape (`GW4Reg.WalkPocketShape`, proved by `PocketMirror.pocketShapeDetStatement`), and a
component chart `c` of a component `C` between them:

* **`landing_notMem_of_pos` / `landing_notMem_of_neg`**: the landing of `c` at `x > 0` is not a point of the left wall
  `range β`, at `x < 0` not a point of the right wall. Proof: with the pocket coordinate `G` of `C` (`c⁻¹ = G(k ·)`,
  GB11ChartBdry), the landing at `x > 0` is `α(u) = G(kx)`, `u > s₁`; were it `β(v)`, the contact order gives
  `t₁ < v`, and `v` is before the closing contact; far out along `ℝ₋` the coordinate leaves `β([0, v])` (it tends to the
  closing contact, resp. to `∞`), so `β⁻¹(G([r₀, 0]))` — connected, `β` being a closed embedding — contains `t₁` and
  a parameter beyond `v`, hence `v`, and `G` takes the value `G(kx)` at a nonpositive point: impossible (`G` injective).
* **`exists_closing_contact_of_shape`**: for bounded `C`, the closing contact `α(U) = β(V) ∈ C̄` comes after every
  landing on both walls (from the frontier description of the shape and the contact order).
* **`pocket_landing_facts`**: both, for every component chart.

So, for Theorem 1.4's walks, no landing of a component chart is a common point of the two walks except at `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkWd

open GW4Reg GB11Chart

theorem mem_Hbar_ofReal (r : ℝ) : (r : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (r : ℂ).im by simp

section Coord

variable {α β : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {s₁ t₁ : ℝ≥0} {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}

/-- The landing of a chart with a pocket coordinate at a real point `x` is `G(kx)`. -/
theorem landing_eq_G (h : IsPocketCoord α β C c s₁ t₁ E ψ G k) {x : ℝ} {p : ℂ}
    (hp : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) : p = G ((k * x : ℝ) : ℂ) := by
  have hx : ((k * x : ℝ) : ℂ) ∈ Hbar := mem_Hbar_ofReal _
  have hm : Tendsto (fun w : ℂ => (k : ℂ) * w) (𝓝[H] (x : ℂ)) (𝓝[Hbar] ((k * x : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun w : ℂ => (k : ℂ) * w) := continuous_const.mul continuous_id
      have := (hcont.tendsto (x : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
      simpa only [ofReal_mul] using this
    · filter_upwards [self_mem_nhdsWithin] with w hw
      change 0 ≤ ((k : ℂ) * w).im
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      exact mul_nonneg h.pos.le (le_of_lt (show (0 : ℝ) < w.im from hw))
  have hlim : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (G ((k * x : ℝ) : ℂ))) :=
    ((h.continuousOn_G _ hx).tendsto.comp hm).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (h.inv_eq w hw).symm)
  have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
  exact tendsto_nhds_unique hp hlim

/-- Far out along `ℝ` the pocket coordinate leaves every compact set disjoint from its excluded set. -/
theorem exists_bound_notMem (h : IsPocketCoord α β C c s₁ t₁ E ψ G k) {K : Set ℂ} (hK : IsCompact K)
    (hKE : Disjoint K E) : ∃ M : ℝ, ∀ r : ℝ, M < |r| → G r ∉ K := by
  have hK' : IsCompact (K ∩ closure C) := hK.inter_right isClosed_closure
  have hsub : K ∩ closure C ⊆ closure C \ E := fun z hz => ⟨hz.2, Set.disjoint_left.1 hKE hz.1⟩
  obtain ⟨M, hM⟩ := hK'.exists_bound_of_continuousOn (h.continuousOn_ψ.mono hsub)
  refine ⟨M, fun r hr hrK => ?_⟩
  have hG := h.mapsTo_G (mem_Hbar_ofReal r)
  have h1 := hM _ ⟨hrK, hG.1⟩
  rw [h.left_inv _ (mem_Hbar_ofReal r), Complex.norm_real, Real.norm_eq_abs] at h1
  linarith

end Coord

section Shape

variable {α β : ℝ≥0 → ℂ} {C : Set ℂ} {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}

/-- **Every wall parameter of a point of `C̄ \ E` precedes the closing contact** (`E` containing the closing
contact of a bounded shape). -/
theorem param_lt_entry (hα : GB11.IsCompleteSimpleFlow α) (hβ : GB11.IsCompleteSimpleFlow β)
    (hord : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hCo : IsOpen C) (hCdis : Disjoint C (range α ∪ range β)) (hs : IsPocketShape α β C s₁ t₁ s₂ t₂)
    {E : Set ℂ} (hE : s₂ ≠ ⊤ → α s₂.toNNReal ∈ E) {p : ℂ} (hp : p ∈ closure C \ E) :
    (∀ r : ℝ≥0, α r = p → (r : ℝ≥0∞) < s₂) ∧ (∀ r : ℝ≥0, β r = p → (r : ℝ≥0∞) < t₂) := by
  by_cases hs₂ : s₂ = ⊤
  · have ht₂ : t₂ = ⊤ := hs.top_iff.1 hs₂
    exact ⟨fun r _ => hs₂ ▸ ENNReal.coe_lt_top, fun r _ => ht₂ ▸ ENNReal.coe_lt_top⟩
  have ht₂ : t₂ ≠ ⊤ := fun h => hs₂ (hs.top_iff.2 h)
  have hent := (hs.entry hs₂).1
  have hES := hE hs₂
  have hfr : ∀ r : ℝ≥0, (α r = p ∨ β r = p) → p ∈ frontier C := by
    intro r hr
    rw [hCo.frontier_eq]
    refine ⟨hp.1, fun hpC => ?_⟩
    rcases hr with hr | hr
    · exact Set.disjoint_left.1 hCdis hpC (Or.inl ⟨r, hr⟩)
    · exact Set.disjoint_left.1 hCdis hpC (Or.inr ⟨r, hr⟩)
  have hs₂e : s₂ = (s₂.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hs₂).symm
  have ht₂e : t₂ = (t₂.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal ht₂).symm
  have hpE : p ≠ α s₂.toNNReal := fun he => hp.2 (he ▸ hES)
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rcases hs.frontier_subset (hfr r (Or.inl hr)) with ⟨r', hr', he⟩ | ⟨r', hr', he⟩
    · have hrr : r' = r := hα.2.1 (he.trans hr.symm)
      subst hrr
      rw [hs₂e] at hr' ⊢
      refine lt_of_le_of_ne hr'.2 fun heq => hpE ?_
      rw [← hr, ENNReal.coe_injective heq]
    · rw [hs₂e]
      rw [ht₂e] at hr'
      rcases (ENNReal.coe_le_coe.1 hr'.2).lt_or_eq with hlt | heq
      · exact ENNReal.coe_lt_coe.2 ((hord r s₂.toNNReal r' t₂.toNNReal (hr.trans he.symm) hent).2 hlt)
      · exact absurd (he.symm.trans (by rw [heq, ← hent])) hpE
  · rcases hs.frontier_subset (hfr r (Or.inr hr)) with ⟨r', hr', he⟩ | ⟨r', hr', he⟩
    · rw [ht₂e]
      rw [hs₂e] at hr'
      rcases (ENNReal.coe_le_coe.1 hr'.2).lt_or_eq with hlt | heq
      · exact ENNReal.coe_lt_coe.2 ((hord r' s₂.toNNReal r t₂.toNNReal (he.trans hr.symm) hent).1 hlt)
      · exact absurd (by rw [← he, heq]) hpE
    · have hrr : r' = r := hβ.2.1 (he.trans hr.symm)
      subst hrr
      rw [ht₂e] at hr' ⊢
      refine lt_of_le_of_ne hr'.2 fun heq => hpE ?_
      rw [← hr, ENNReal.coe_injective heq, ← hent]

variable {c : Chart} {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}

/-- **A positive landing is not on the left wall.** -/
theorem landing_notMem_of_pos (hα : GB11.IsCompleteSimpleFlow α) (hβ : GB11.IsCompleteSimpleFlow β)
    (hord : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hCo : IsOpen C) (hCdis : Disjoint C (range α ∪ range β)) (hs : IsPocketShape α β C s₁ t₁ s₂ t₂)
    (h : IsPocketCoord α β C c s₁ t₁ E ψ G k) (hE : s₂ ≠ ⊤ → α s₂.toNNReal ∈ E)
    (hE' : ∀ z ∈ E, s₂ ≠ ⊤ ∧ z = α s₂.toNNReal) {x : ℝ} (hx : 0 < x) {p : ℂ}
    (hp : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) : p ∉ range β := by
  rintro ⟨v, rfl⟩
  have hpG := landing_eq_G h hp
  have hkx : 0 < k * x := mul_pos h.pos hx
  obtain ⟨u, hu, hue⟩ := h.pos_arc (k * x) hkx
  have hvt : t₁ < v := (hord s₁ u t₁ v hs.contact (hue.trans hpG.symm)).1 hu
  have hpm : β v ∈ closure C \ E := hpG ▸ h.mapsTo_G (mem_Hbar_ofReal _)
  have hv2 : (v : ℝ≥0∞) < t₂ := (param_lt_entry hα hβ hord hCo hCdis hs hE hpm).2 v rfl
  have hK : IsCompact (β '' Icc 0 v) := isCompact_Icc.image hβ.1
  have hKE : Disjoint (β '' Icc 0 v) E := by
    rw [Set.disjoint_left]
    rintro z ⟨w, hw, rfl⟩ hzE
    obtain ⟨hs2, hz⟩ := hE' _ hzE
    have ht2 : t₂ ≠ ⊤ := fun ht => hs2 (hs.top_iff.2 ht)
    have hw2 : w = t₂.toNNReal := hβ.2.1 (hz.trans (hs.entry hs2).1)
    have hle : t₂ ≤ (v : ℝ≥0∞) := by
      rw [← ENNReal.coe_toNNReal ht2, ← hw2]
      exact ENNReal.coe_le_coe.2 hw.2
    exact absurd hv2 (not_lt.2 hle)
  obtain ⟨M, hM⟩ := exists_bound_notMem h hK hKE
  set r₀ : ℝ := -(|M| + 1) with hr₀def
  have hr₀ : r₀ < 0 := by rw [hr₀def]; linarith [abs_nonneg M]
  have hr₀M : M < |r₀| := by
    rw [hr₀def, abs_neg, abs_of_pos (by linarith [abs_nonneg M])]; linarith [le_abs_self M]
  obtain ⟨w₀, hw₀, hw₀e⟩ := h.neg_arc r₀ hr₀
  have hw₀v : v < w₀ := by
    by_contra hle
    exact hM r₀ hr₀M ⟨w₀, ⟨zero_le, not_lt.1 hle⟩, hw₀e⟩
  have hG0 : G ((0 : ℝ) : ℂ) = β t₁ := by rw [ofReal_zero, h.G_zero, hs.contact]
  set Seg : Set ℂ := (fun r : ℝ => G r) '' Icc r₀ 0 with hSegdef
  have hSeg : IsPreconnected Seg := isPreconnected_Icc.image _
    (h.continuousOn_G.comp continuous_ofReal.continuousOn (fun r _ => mem_Hbar_ofReal r))
  have hSegβ : Seg ⊆ range β := by
    rintro _ ⟨r, hr, rfl⟩
    rcases hr.2.lt_or_eq with hr0 | hr0
    · obtain ⟨w, -, hw⟩ := h.neg_arc r hr0
      exact ⟨w, hw⟩
    · exact ⟨t₁, by rw [hr0]; exact hG0.symm⟩
  have hS : IsPreconnected (β ⁻¹' Seg) :=
    (isClosedEmbedding_of_isCompleteSimpleFlow hβ).isInducing.isPreconnected_image.1
      ((image_preimage_eq_of_subset hSegβ).symm ▸ hSeg)
  have ht₁S : t₁ ∈ β ⁻¹' Seg := ⟨0, ⟨hr₀.le, le_rfl⟩, hG0⟩
  have hw₀S : w₀ ∈ β ⁻¹' Seg := ⟨r₀, ⟨le_rfl, hr₀.le⟩, hw₀e.symm⟩
  obtain ⟨r, hr, hre⟩ := hS.Icc_subset ht₁S hw₀S ⟨hvt.le, hw₀v.le⟩
  have hrk := ofReal_injective (h.injOn_G (mem_Hbar_ofReal r) (mem_Hbar_ofReal (k * x)) (hre.trans hpG))
  linarith [hr.2]

/-- **A negative landing is not on the right wall.** -/
theorem landing_notMem_of_neg (hα : GB11.IsCompleteSimpleFlow α) (hβ : GB11.IsCompleteSimpleFlow β)
    (hord : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hCo : IsOpen C) (hCdis : Disjoint C (range α ∪ range β)) (hs : IsPocketShape α β C s₁ t₁ s₂ t₂)
    (h : IsPocketCoord α β C c s₁ t₁ E ψ G k) (hE : s₂ ≠ ⊤ → α s₂.toNNReal ∈ E)
    (hE' : ∀ z ∈ E, s₂ ≠ ⊤ ∧ z = α s₂.toNNReal) {x : ℝ} (hx : x < 0) {p : ℂ}
    (hp : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) : p ∉ range α := by
  rintro ⟨u, rfl⟩
  have hpG := landing_eq_G h hp
  have hkx : k * x < 0 := mul_neg_of_pos_of_neg h.pos hx
  obtain ⟨v, hv, hve⟩ := h.neg_arc (k * x) hkx
  have hus : s₁ < u := (hord s₁ u t₁ v hs.contact (hpG.trans hve.symm)).2 hv
  have hpm : α u ∈ closure C \ E := hpG ▸ h.mapsTo_G (mem_Hbar_ofReal _)
  have hu2 : (u : ℝ≥0∞) < s₂ := (param_lt_entry hα hβ hord hCo hCdis hs hE hpm).1 u rfl
  have hK : IsCompact (α '' Icc 0 u) := isCompact_Icc.image hα.1
  have hKE : Disjoint (α '' Icc 0 u) E := by
    rw [Set.disjoint_left]
    rintro z ⟨w, hw, rfl⟩ hzE
    obtain ⟨hs2, hz⟩ := hE' _ hzE
    have hw2 : w = s₂.toNNReal := hα.2.1 hz
    have hle : s₂ ≤ (u : ℝ≥0∞) := by
      rw [← ENNReal.coe_toNNReal hs2, ← hw2]
      exact ENNReal.coe_le_coe.2 hw.2
    exact absurd hu2 (not_lt.2 hle)
  obtain ⟨M, hM⟩ := exists_bound_notMem h hK hKE
  set r₀ : ℝ := |M| + 1 with hr₀def
  have hr₀ : 0 < r₀ := by rw [hr₀def]; linarith [abs_nonneg M]
  have hr₀M : M < |r₀| := by rw [abs_of_pos hr₀, hr₀def]; linarith [le_abs_self M]
  obtain ⟨w₀, hw₀, hw₀e⟩ := h.pos_arc r₀ hr₀
  have hw₀u : u < w₀ := by
    by_contra hle
    exact hM r₀ hr₀M ⟨w₀, ⟨zero_le, not_lt.1 hle⟩, hw₀e⟩
  have hG0 : G ((0 : ℝ) : ℂ) = α s₁ := by rw [ofReal_zero, h.G_zero]
  set Seg : Set ℂ := (fun r : ℝ => G r) '' Icc 0 r₀ with hSegdef
  have hSeg : IsPreconnected Seg := isPreconnected_Icc.image _
    (h.continuousOn_G.comp continuous_ofReal.continuousOn (fun r _ => mem_Hbar_ofReal r))
  have hSegα : Seg ⊆ range α := by
    rintro _ ⟨r, hr, rfl⟩
    rcases hr.1.lt_or_eq with hr0 | hr0
    · obtain ⟨w, -, hw⟩ := h.pos_arc r hr0
      exact ⟨w, hw⟩
    · exact ⟨s₁, by rw [← hr0]; exact hG0.symm⟩
  have hS : IsPreconnected (α ⁻¹' Seg) :=
    (isClosedEmbedding_of_isCompleteSimpleFlow hα).isInducing.isPreconnected_image.1
      ((image_preimage_eq_of_subset hSegα).symm ▸ hSeg)
  have hs₁S : s₁ ∈ α ⁻¹' Seg := ⟨0, ⟨le_rfl, hr₀.le⟩, hG0⟩
  have hw₀S : w₀ ∈ α ⁻¹' Seg := ⟨r₀, ⟨hr₀.le, le_rfl⟩, hw₀e.symm⟩
  obtain ⟨r, hr, hre⟩ := hS.Icc_subset hs₁S hw₀S ⟨hus.le, hw₀u.le⟩
  have hrk := ofReal_injective (h.injOn_G (mem_Hbar_ofReal r) (mem_Hbar_ofReal (k * x)) (hre.trans hpG))
  linarith [hr.1]

end Shape

/-- **The landing facts of every component chart** (see the module docstring): landings at `x > 0` avoid the left wall,
at `x < 0` the right wall; a bounded component has a closing contact `α U = β V ∈ C̄` after every landing. -/
theorem pocket_landing_facts {α β : ℝ≥0 → ℂ} (hα : GB11.IsCompleteSimpleFlow α) (hβ : GB11.IsCompleteSimpleFlow β)
    (hord : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hW : WalkPocketShape α β) {C : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β))
    {c : Chart} (hc : IsComponentChart (range α) (range β) C c) :
    (∀ (x : ℝ) (p : ℂ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → (0 < x → p ∉ range β) ∧ (x < 0 → p ∉ range α)) ∧
    (Bornology.IsBounded C → ∃ U V : ℝ≥0, α U = β V ∧ α U ∈ closure C ∧
      ∀ (x : ℝ) (p : ℂ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) →
        (∀ r : ℝ≥0, α r = p → r < U) ∧ (∀ r : ℝ≥0, β r = p → r < V)) := by
  obtain ⟨s₁, t₁, s₂, t₂, hs⟩ := hW.1 C hC
  have hCo : IsOpen C := GW4Reg.isOpen_of_mem_betweenComponents (GW4Reg.isClosed_range_of_isCompleteSimpleFlow hα)
    (GW4Reg.isClosed_range_of_isCompleteSimpleFlow hβ) hC
  have hCdis : Disjoint C (range α ∪ range β) := Set.disjoint_left.2 fun z hz hzw =>
    (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).2 hzw
  obtain ⟨p₀, hp₀, -, -⟩ := hc.2.2.2.2.1 0
  have hp₀' : Tendsto c.2.1 (𝓝[H] (0 : ℂ)) (𝓝 p₀) := by simpa only [ofReal_zero] using hp₀
  have hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (α s₁)) := (hW.2.1 C hC s₁ t₁ s₂ t₂ hs c hc p₀ hp₀') ▸ hp₀'
  -- the coordinate, with its excluded set
  have key : ∃ (E : Set ℂ) (ψ G : ℂ → ℂ) (k : ℝ), IsPocketCoord α β C c s₁ t₁ E ψ G k ∧
      (s₂ ≠ ⊤ → α s₂.toNNReal ∈ E) ∧ ∀ z ∈ E, s₂ ≠ ⊤ ∧ z = α s₂.toNNReal := by
    by_cases hs₂ : s₂ = ⊤
    · obtain ⟨ψ, G, k, hpc, -, -⟩ := exists_isPocketCoord_of_unbounded hα hβ hord hC hs hs₂ hc hxC
      exact ⟨∅, ψ, G, k, hpc, fun h => absurd hs₂ h, fun z hz => absurd hz (notMem_empty z)⟩
    · obtain ⟨ψ, G, k, hpc, -, -⟩ := exists_isPocketCoord_of_bounded hα hβ hord hC hs hs₂ hc hxC
      exact ⟨{α s₂.toNNReal}, ψ, G, k, hpc, fun _ => mem_singleton _,
        fun z hz => ⟨hs₂, mem_singleton_iff.1 hz⟩⟩
  obtain ⟨E, ψ, G, k, hpc, hE, hE'⟩ := key
  refine ⟨fun x p hp => ⟨fun hx => landing_notMem_of_pos hα hβ hord hCo hCdis hs hpc hE hE' hx hp,
    fun hx => landing_notMem_of_neg hα hβ hord hCo hCdis hs hpc hE hE' hx hp⟩, fun hb => ?_⟩
  have hs₂ : s₂ ≠ ⊤ := fun h => hs.unbounded h hb
  have ht₂ : t₂ ≠ ⊤ := fun h => hs₂ (hs.top_iff.2 h)
  obtain ⟨hent, hcl, -⟩ := hs.entry hs₂
  refine ⟨s₂.toNNReal, t₂.toNNReal, hent, hcl, fun x p hp => ?_⟩
  have hpm : p ∈ closure C \ E := (landing_eq_G hpc hp) ▸ hpc.mapsTo_G (mem_Hbar_ofReal _)
  obtain ⟨h1, h2⟩ := param_lt_entry hα hβ hord hCo hCdis hs hE hpm
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · have := h1 r hr
    rwa [← ENNReal.coe_toNNReal hs₂, ENNReal.coe_lt_coe] at this
  · have := h2 r hr
    rwa [← ENNReal.coe_toNNReal ht₂, ENNReal.coe_lt_coe] at this

end InteractingSLE.Theorem14.WalkWd
