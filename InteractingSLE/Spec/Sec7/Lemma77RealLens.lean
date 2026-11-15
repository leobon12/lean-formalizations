/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77RealConf

/-!
# Lemma 7.7: no minimal lens, real corners included (Aux. lemmas 71–72)

Packet PROVE-LEMMA77-B (specification §7.2, Aux. lemmas 71–72, pp. 276–279, `source/spec/p241-288.md#aux-71`).

Two adjacent minimal contacts `p = α(a) = β(b)`, `q = α(c) = β(d)` (`a < c`, `d < b`) bound a lens. As in
`Lemma77Lens.lean`, the θ-curve formed by the two lens sides and the third arc `α([0, a])⁻¹ · ℓ · β([0, d])` (its
degenerate pieces dropped when `a = 0` or `d = 0`, `exists_third_arc`) puts one lens side inside the closing curve
through the other (the third arc dips below `ℝ`, so it is never inside):

* `α((a, c))` inside `α([0, a]) ∪ β([0, b]) ∪ L`: at an interior corner `p` this is the forbidden-side witness
  (`false_of_inside`); at a real corner `p`, `(a, b)` is the common first contact of `α|[0, c']` and `β|[0, b]`
  (`a < c' < c`) and its continuation points inside the closing curve are off the joint unbounded domain, which
  `false_of_notMem_of_real` excludes;
* `β((d, b))` inside `β([0, d]) ∪ α([0, c]) ∪ L`: the reflected alternative at `q`.

`realCornerLensExclusion` proves the proposition `RealCornerLensExclusion` of `Lemma77Main.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart Foundations.ThetaCurve

/-- The joint unbounded domain lies outside every closing curve through the lower half-plane. -/
theorem H_diff_fillH_subset_jordanOut {K L : Set ℂ} (hK : IsCompact K) (hLim : ∀ z ∈ L, z.im ≤ 0) :
    H \ fillH K ⊆ WangWu.jordanOut (K ∪ L) :=
  WangWu.subset_jordanOut_of_isPreconnected (isPreconnected_H_diff_fillH hK.isClosed hK.isBounded)
    (not_isBounded_H_diff_fillH hK.isBounded) (Set.disjoint_left.2 fun z hz hzKL => by
      rcases hzKL with h | h
      · exact (H_diff_fillH_subset_H_diff hK.isClosed hz).2 h
      · exact absurd (hLim z h) (not_le.2 (show (0 : ℝ) < z.im from hz.1)))

/-- **The third arc of a minimal lens**: `α([0, a])⁻¹ · ℓ · β([0, d])` from `α(a)` to `β(d)`, with the degenerate
pieces dropped when `a = 0` or `d = 0`; its open part contains the lowest point of `ℓ`. -/
theorem exists_third_arc {α β : ℝ≥0 → ℂ} {x₁ x₂ : ℝ} (hx : x₂ < x₁) {a d : ℝ≥0}
    (hαc : ContinuousOn α (Icc 0 a)) (hαi : InjOn α (Icc 0 a)) (hβc : ContinuousOn β (Icc 0 d))
    (hβi : InjOn β (Icc 0 d)) (hx₁ : α 0 = x₁) (hx₂ : β 0 = x₂)
    (h₁ : α '' Icc 0 a ∩ lowerArc x₂ x₁ ⊆ {(x₁ : ℂ)})
    (h₂ : (α '' Icc 0 a ∪ lowerArc x₂ x₁) ∩ β '' Icc 0 d ⊆ {(x₂ : ℂ)}) :
    ∃ uA : ℝ → ℂ, IsArcFrom uA (α a) (β d) ∧ arc uA = α '' Icc 0 a ∪ lowerArc x₂ x₁ ∪ β '' Icc 0 d ∧
      ∃ y ∈ Ioo (0 : ℝ) 1, uA y = lowerArcPath x₂ x₁ (1 / 2) := by
  set ℓ := lowerArcPath x₂ x₁ with hℓ
  have hℓa : IsArcFrom ℓ (x₁ : ℂ) (x₂ : ℂ) := isArcFrom_lowerArcPath hx
  have harcℓ : arc ℓ = lowerArc x₂ x₁ := rfl
  have hx₁L : (x₁ : ℂ) ∈ lowerArc x₂ x₁ := left_mem_lowerArc
  have hx₂L : (x₂ : ℂ) ∈ lowerArc x₂ x₁ := right_mem_lowerArc
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ a) with ha0 | ha0 <;>
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ d) with hd0 | hd0
  · subst ha0 hd0
    refine ⟨ℓ, by rw [hx₁, hx₂]; exact hℓa, ?_, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    rw [harcℓ, Icc_self, image_singleton, image_singleton, hx₁, hx₂,
      union_eq_right.2 (singleton_subset_iff.2 hx₁L), union_eq_left.2 (singleton_subset_iff.2 hx₂L)]
  · subst ha0
    have hβF : IsArcFrom (segArc β 0 d) (x₂ : ℂ) (β d) := by
      have := isArcFrom_segArc hd0 hβc hβi
      rwa [hx₂] at this
    have hint : arc ℓ ∩ arc (segArc β 0 d) ⊆ {(x₂ : ℂ)} := by
      rw [harcℓ, arc_segArc zero_le]
      exact fun z hz => h₂ ⟨Or.inr hz.1, hz.2⟩
    refine ⟨Sec6.arcJoin ℓ (segArc β 0 d), ?_, ?_, 1 / 4, ⟨by norm_num, by norm_num⟩, ?_⟩
    · rw [hx₁]; exact isArcFrom_arcJoin hℓa hβF hint
    · rw [arc_arcJoin hℓa hβF, harcℓ, arc_segArc zero_le, Icc_self, image_singleton, hx₁,
        union_eq_right.2 (singleton_subset_iff.2 hx₁L)]
    · simp only [Sec6.arcJoin]
      norm_num
  · subst hd0
    have hαR : IsArcFrom (Sec6.arcRev (segArc α 0 a)) (α a) (x₁ : ℂ) := by
      have := isArcFrom_arcRev (isArcFrom_segArc ha0 hαc hαi)
      rwa [hx₁] at this
    have hint : arc (Sec6.arcRev (segArc α 0 a)) ∩ arc ℓ ⊆ {(x₁ : ℂ)} := by
      rw [arc_arcRev, arc_segArc zero_le, harcℓ]
      exact h₁
    refine ⟨Sec6.arcJoin (Sec6.arcRev (segArc α 0 a)) ℓ, ?_, ?_, 3 / 4, ⟨by norm_num, by norm_num⟩, ?_⟩
    · rw [hx₂]; exact isArcFrom_arcJoin hαR hℓa hint
    · rw [arc_arcJoin hαR hℓa, arc_arcRev, arc_segArc zero_le, harcℓ, Icc_self, image_singleton, hx₂]
      exact (union_eq_left.2 (singleton_subset_iff.2
        (show (x₂ : ℂ) ∈ α '' Icc 0 a ∪ lowerArc x₂ x₁ from Or.inr hx₂L))).symm
    · simp only [Sec6.arcJoin]
      norm_num
  · have hαR : IsArcFrom (Sec6.arcRev (segArc α 0 a)) (α a) (x₁ : ℂ) := by
      have := isArcFrom_arcRev (isArcFrom_segArc ha0 hαc hαi)
      rwa [hx₁] at this
    have hβF : IsArcFrom (segArc β 0 d) (x₂ : ℂ) (β d) := by
      have := isArcFrom_segArc hd0 hβc hβi
      rwa [hx₂] at this
    have hint₁ : arc (Sec6.arcRev (segArc α 0 a)) ∩ arc ℓ ⊆ {(x₁ : ℂ)} := by
      rw [arc_arcRev, arc_segArc zero_le, harcℓ]
      exact h₁
    have hinner := isArcFrom_arcJoin hαR hℓa hint₁
    have hint₂ : arc (Sec6.arcJoin (Sec6.arcRev (segArc α 0 a)) ℓ) ∩ arc (segArc β 0 d) ⊆ {(x₂ : ℂ)} := by
      rw [arc_arcJoin hαR hℓa, arc_arcRev, arc_segArc zero_le, harcℓ, arc_segArc zero_le]
      exact h₂
    refine ⟨Sec6.arcJoin (Sec6.arcJoin (Sec6.arcRev (segArc α 0 a)) ℓ) (segArc β 0 d),
      isArcFrom_arcJoin hinner hβF hint₂, ?_, 3 / 8, ⟨by norm_num, by norm_num⟩, ?_⟩
    · rw [arc_arcJoin hinner hβF, arc_arcJoin hαR hℓa, arc_arcRev, arc_segArc zero_le, harcℓ,
        arc_segArc zero_le]
    · simp only [Sec6.arcJoin]
      norm_num

/-- **Aux. lemma 72, every corner.** Two good paths from `x₁ > x₂` cannot have two adjacent minimal contacts
`p = α(a) = β(b)`, `q = α(c) = β(d)` if Lemma 7.6's conclusion holds (both halves) at every pair of rational stops;
the corners may be real points. -/
theorem false_of_adjacent_minimalContacts {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁) {A B : ℝ≥0}
    (hA : (A : ℝ≥0∞) ≤ ζ₁) (hB : (B : ℝ≥0∞) ≤ ζ₂) {a b c d : ℝ≥0}
    (hab : (a, b) ∈ Sec7.minimalContacts α A β B) (hcd : (c, d) ∈ Sec7.minimalContacts α A β B)
    (hac : a < c) (hgap : ∀ p ∈ Sec7.minimalContacts α A β B, p.1 ∉ Ioo a c)
    (hbar₁ : ∀ q q' : ℚ, FirstExitBarrier α (truncAt ζ₁ (q : ℝ).toNNReal) β ζ₂ (truncAt ζ₂ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁))
    (hbar₂ : ∀ q q' : ℚ, FirstExitBarrier β (truncAt ζ₂ (q : ℝ).toNNReal) α ζ₁ (truncAt ζ₁ (q' : ℝ).toNNReal)
      (lowerArc x₂ x₁)) : False := by
  -- basic facts
  have hα : ContinuousOn α (Icc 0 A) := IsPathGood.continuousOn_Icc hp₁ hA
  have hβ : ContinuousOn β (Icc 0 B) := IsPathGood.continuousOn_Icc hp₂ hB
  have hαi : InjOn α (Icc 0 A) := IsPathGood.injOn_Icc hp₁ hA
  have hβi : InjOn β (Icc 0 B) := IsPathGood.injOn_Icc hp₂ hB
  have hdb : d < b := snd_lt_of_mem_minimalContacts hab hcd hac
  have hcA : c ≤ A := hcd.1.1.2
  have hbB : b ≤ B := hab.1.2.1.2
  have hpq : α a = β b := hab.1.2.2
  have hqq : α c = β d := hcd.1.2.2
  have hx₁ : α 0 = x₁ := IsPathGood.zero hp₁
  have hx₂ : β 0 = x₂ := IsPathGood.zero hp₂
  have hsep := adjacent_minimalContacts hα hβ hab hcd hac hgap
  have hnc : ∀ s t : ℝ≥0, s ≤ A → t ≤ B → α s = β t → s < c → t < b → False := fun s t hs ht hst hsc htb =>
    lens_no_contact hβi hα hβ hab hgap hs ht hst hsc htb
  have hαA : ∀ s ∈ Icc (0 : ℝ≥0) c, s ≤ A := fun s hs => hs.2.trans hcA
  have hβB : ∀ t ∈ Icc (0 : ℝ≥0) b, t ≤ B := fun t ht => ht.2.trans hbB
  set L := lowerArc x₂ x₁ with hL
  have hLre : ∀ z ∈ L, 0 ≤ z.im → z = x₁ ∨ z = x₂ := fun z hz hz0 =>
    (im_le_zero_of_mem_lowerArc hz).2 (le_antisymm (im_le_zero_of_mem_lowerArc hz).1 hz0)
  have hLim : ∀ z ∈ L, z.im ≤ 0 := fun z hz => (im_le_zero_of_mem_lowerArc hz).1
  have him₁ : ∀ s ∈ Icc (0 : ℝ≥0) c, 0 ≤ (α s).im := fun s hs =>
    IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 (hαA s hs)).trans hA)
  have him₂ : ∀ t ∈ Icc (0 : ℝ≥0) b, 0 ≤ (β t).im := fun t ht =>
    IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 (hβB t ht)).trans hB)
  have hcα : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ c → ContinuousOn α (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hα.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hcA)⟩ : s ∈ Icc 0 A)
  have hiα : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ c → InjOn α (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hαi.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hcA)⟩ : s ∈ Icc 0 A)
  have hcβ : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ b → ContinuousOn β (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hβ.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hbB)⟩ : s ∈ Icc 0 B)
  have hiβ : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ b → InjOn β (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hβi.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hbB)⟩ : s ∈ Icc 0 B)
  -- the two lens sides
  set wA := segArc α a c with hwA
  set vA := Sec6.arcRev (segArc β d b) with hvA
  have hw : IsArcFrom wA (α a) (α c) := isArcFrom_segArc hac (hcα le_rfl) (hiα le_rfl)
  have hv : IsArcFrom vA (α a) (α c) := by
    have := isArcFrom_arcRev (isArcFrom_segArc hdb (hcβ le_rfl) (hiβ le_rfl))
    rwa [← hpq, ← hqq] at this
  have harcw : arc wA = α '' Icc a c := arc_segArc hac.le
  have harcv : arc vA = β '' Icc d b := by rw [hvA, arc_arcRev, arc_segArc hdb.le]
  -- contacts with the seeds
  have hx₂α : ∀ s ∈ Icc (0 : ℝ≥0) c, α s = x₂ → s = c := fun s hs h => by
    by_contra hne
    exact hnc s 0 (hαA s hs) zero_le (by rw [h, hx₂]) (lt_of_le_of_ne hs.2 hne) (zero_le.trans_lt hdb)
  have hx₁β : ∀ t ∈ Icc (0 : ℝ≥0) b, β t = x₁ → t = b := fun t ht h => by
    by_contra hne
    exact hnc 0 t zero_le (hβB t ht) (by rw [h, hx₁]) (zero_le.trans_lt hac) (lt_of_le_of_ne ht.2 hne)
  -- the third arc
  have hint₁ : α '' Icc 0 a ∩ L ⊆ {(x₁ : ℂ)} := by
    rintro z ⟨⟨s, hs, rfl⟩, hz₂⟩
    have hsc : s ∈ Icc (0 : ℝ≥0) c := ⟨hs.1, hs.2.trans hac.le⟩
    rcases hLre _ hz₂ (him₁ s hsc) with h | h
    · exact h
    · exact absurd (hx₂α s hsc h ▸ hs.2) (not_le.2 hac)
  have hint₂ : (α '' Icc 0 a ∪ L) ∩ β '' Icc 0 d ⊆ {(x₂ : ℂ)} := by
    rintro z ⟨hz₁, ⟨t, ht, rfl⟩⟩
    rcases hz₁ with ⟨s, hs, hst⟩ | hz₁
    · exact (Set.disjoint_left.1 hsep.2.1 ⟨s, hs, hst⟩ ⟨t, ht, rfl⟩).elim
    · have htb : t ∈ Icc (0 : ℝ≥0) b := ⟨ht.1, ht.2.trans hdb.le⟩
      rcases hLre _ hz₁ (him₂ t htb) with h | h
      · exact absurd (hx₁β t htb h ▸ ht.2) (not_le.2 hdb)
      · exact h
  obtain ⟨uA, hu, harcu, y₀, hy₀, hy₀ℓ⟩ := exists_third_arc hx (hcα hac.le) (hiα hac.le) (hcβ hdb.le)
    (hiβ hdb.le) hx₁ hx₂ hint₁ hint₂
  rw [← hqq] at hu
  -- pairwise intersections
  have huv : arc uA ∩ arc vA ⊆ {α a, α c} := by
    rintro z ⟨hz₁, hz₂⟩
    rw [harcv] at hz₂
    obtain ⟨t, ht, rfl⟩ := hz₂
    have htb : t ∈ Icc (0 : ℝ≥0) b := ⟨zero_le, ht.2⟩
    rw [harcu] at hz₁
    rcases hz₁ with (hz₁ | hz₁) | hz₁
    · have : β t ∈ α '' Icc 0 a ∩ β '' Icc d b := ⟨hz₁, ⟨t, ht, rfl⟩⟩
      rw [hsep.2.2.1] at this
      exact Or.inl this
    · rcases hLre _ hz₁ (him₂ t htb) with h | h
      · rw [hx₁β t htb h, ← hpq]; exact Or.inl rfl
      · rw [← hx₂] at h
        have h0 := hβi ⟨zero_le, hβB t htb⟩ (⟨le_rfl, zero_le⟩ : (0 : ℝ≥0) ∈ Icc 0 B) h
        have htd : t = d := le_antisymm (by rw [h0]; exact zero_le) ht.1
        rw [htd, ← hqq]; exact Or.inr rfl
    · obtain ⟨t', ht', htt'⟩ := hz₁
      have := hβi ⟨zero_le, hβB t' ⟨ht'.1, ht'.2.trans hdb.le⟩⟩ ⟨zero_le, hβB t htb⟩ htt'
      rw [← this, le_antisymm ht'.2 (this ▸ ht.1), ← hqq]
      exact Or.inr rfl
  have huw : arc uA ∩ arc wA ⊆ {α a, α c} := by
    rintro z ⟨hz₁, hz₂⟩
    rw [harcw] at hz₂
    obtain ⟨s, hs, rfl⟩ := hz₂
    have hsc : s ∈ Icc (0 : ℝ≥0) c := ⟨zero_le, hs.2⟩
    rw [harcu] at hz₁
    rcases hz₁ with (hz₁ | hz₁) | hz₁
    · obtain ⟨s', hs', hss'⟩ := hz₁
      have := hαi ⟨zero_le, hαA s' ⟨hs'.1, hs'.2.trans hac.le⟩⟩ ⟨zero_le, hαA s hsc⟩ hss'
      rw [← this, le_antisymm hs'.2 (this ▸ hs.1)]
      exact Or.inl rfl
    · rcases hLre _ hz₁ (him₁ s hsc) with h | h
      · rw [← hx₁] at h
        have h0 := hαi ⟨zero_le, hαA s hsc⟩ (⟨le_rfl, zero_le⟩ : (0 : ℝ≥0) ∈ Icc 0 A) h
        have hsa : s = a := le_antisymm (by rw [h0]; exact zero_le) hs.1
        rw [hsa]; exact Or.inl rfl
      · rw [hx₂α s hsc h]; exact Or.inr rfl
    · have : α s ∈ β '' Icc 0 d ∩ α '' Icc a c := ⟨hz₁, ⟨s, hs, rfl⟩⟩
      rw [hsep.2.2.2] at this
      exact Or.inr this
  have hvw : arc vA ∩ arc wA ⊆ {α a, α c} := by
    rw [harcv, harcw, inter_comm, hsep.1]
  -- the θ-curve theorem
  rcases exists_arcInt_subset_jordanIn hu hv hw huv huw hvw with hin | hin | hin
  · -- the first lens side is inside: `β` arrives at `p` from the right side of `α`
    have hJ : arc uA ∪ arc vA = α '' Icc 0 a ∪ β '' Icc 0 b ∪ L := by
      rw [harcu, harcv, ← Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ d) hdb.le, image_union]
      ext z; simp only [mem_union]; tauto
    by_cases hpH : α a ∈ H
    · obtain ⟨v₀, hav₀, hv₀c⟩ := exists_between hac
      refine false_of_inside hp₁ hp₂ hav₀ ((ENNReal.coe_le_coe.2 (hv₀c.le.trans hcA)).trans hA)
        ((ENNReal.coe_le_coe.2 hbB).trans hB) hpq hpH (fun v hv => ?_) (fun s t hs ht hst => ?_) hbar₁
      · rw [← hJ]
        exact hin (mem_arcInt_segArc hac ⟨hv.1, hv.2.trans_lt hv₀c⟩)
      · exact hnc s t ((hs.trans hv₀c).le.trans hcA) (ht.le.trans hbB) hst (hs.trans hv₀c) ht
    -- a real corner: `(a, b)` is the first contact of `α|[0, c']` and `β|[0, b]`
    obtain ⟨c', hac', hc'c⟩ := exists_between hac
    have hc'ζ : (c' : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 (hc'c.le.trans hcA)).trans hA
    have hbζ : (b : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 hbB).trans hB
    have hfc' : IsFirstContact α c' β b a b := by
      refine ⟨ENNReal.coe_le_coe.2 hac'.le, le_rfl, hpq, fun s t hs ht hst => ?_⟩
      have hs' : s ≤ c' := ENNReal.coe_le_coe.1 hs
      have ht' : t ≤ b := ENNReal.coe_le_coe.1 ht
      rcases eq_or_lt_of_le ht' with htb | htb
      · have := hαi ⟨zero_le, hs'.trans (hc'c.le.trans hcA)⟩ ⟨zero_le, hac.le.trans hcA⟩
          (hst.trans (by rw [htb]; exact hpq.symm))
        exact ⟨this.ge, htb.ge⟩
      · exact (hnc s t (hs'.trans (hc'c.le.trans hcA)) (ht'.trans hbB) hst (hs'.trans_lt hc'c) htb).elim
    have hcK : IsCompact (α '' Icc 0 a ∪ β '' Icc 0 b) :=
      (IsPathGood.isCompact_image hp₁ ((ENNReal.coe_le_coe.2 hac'.le).trans hc'ζ)).union
        (IsPathGood.isCompact_image hp₂ hbζ)
    refine false_of_notMem_of_real (IsPathGood.mono hp₁ hc'ζ) (IsPathGood.mono hp₂ hbζ) isCompact_lowerArc
      isPreconnected_lowerArc hLim left_mem_lowerArc right_mem_lowerArc hfc' hpH hac' le_rfl
      (fun v hv _ hvD => ?_) (barrier_of_truncAt hc'ζ hbζ hbar₁)
    have hvin : α v ∈ WangWu.jordanIn (α '' Icc 0 a ∪ β '' Icc 0 b ∪ L) := by
      rw [← hJ]
      exact hin (mem_arcInt_segArc hac ⟨hv.1, hv.2.trans_lt hc'c⟩)
    exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) hvin
      (H_diff_fillH_subset_jordanOut hcK hLim hvD)
  · -- the third arc inside the lens: impossible, its lower point is outside
    have hmid : uA y₀ ∈ arcInt uA := ⟨y₀, hy₀, rfl⟩
    have hlow : (lowerArcPath x₂ x₁ (1 / 2)).im < 0 := by
      rw [lowerArcPath]
      simp only [Sec6.arcJoin, Sec6.segPath]
      norm_num
    have hz := hin hmid
    rw [hy₀ℓ] at hz
    have hout : {z : ℂ | z.im < 0} ⊆ WangWu.jordanOut (arc vA ∪ arc wA) := by
      refine WangWu.subset_jordanOut_of_isPreconnected ?_ ?_ ?_
      · exact (convex_halfSpace_lt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
      · intro hb
        obtain ⟨R, hR⟩ := hb.subset_closedBall 0
        set y : ℂ := ((-(|R| + 1) : ℝ) : ℂ) * I with hy
        have hyim : y.im = -(|R| + 1) := by
          simp only [hy, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        have hy0 : y.im < 0 := by rw [hyim]; linarith [abs_nonneg R]
        have hyR := mem_closedBall_zero_iff.1 (hR hy0)
        have hny : ‖y‖ = |R| + 1 := by
          rw [hy, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_neg (by linarith [abs_nonneg R])]
          ring
        rw [hny] at hyR
        linarith [le_abs_self R]
      · refine Set.disjoint_left.2 fun z hz hzJ => ?_
        rw [harcv, harcw] at hzJ
        have hz0 : z.im < 0 := hz
        rcases hzJ with ⟨t, ht, rfl⟩ | ⟨s, hs, rfl⟩
        · exact absurd (him₂ t ⟨zero_le, ht.2⟩) (not_le.2 hz0)
        · exact absurd (him₁ s ⟨zero_le, hs.2⟩) (not_le.2 hz0)
    exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) hz (hout hlow)
  · -- the second lens side is inside: `α` arrives at `q` from the left side of `β`
    have hJ : arc uA ∪ arc wA = β '' Icc 0 d ∪ α '' Icc 0 c ∪ L := by
      rw [harcu, harcw, ← Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ a) hac.le, image_union]
      ext z; simp only [mem_union]; tauto
    have hinβ : ∀ v ∈ Ioo d b, β v ∈ WangWu.jordanIn (β '' Icc 0 d ∪ α '' Icc 0 c ∪ L) := by
      intro v hv
      rw [← hJ]
      have hmem := mem_arcInt_segArc (η := β) hdb hv
      refine hin ?_
      obtain ⟨y, hy, hyv⟩ := hmem
      exact ⟨1 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simp [hvA, Sec6.arcRev, hyv]⟩
    by_cases hqH : α c ∈ H
    · obtain ⟨v₀, hdv₀, hv₀b⟩ := exists_between hdb
      refine false_of_inside hp₂ hp₁ hdv₀ ((ENNReal.coe_le_coe.2 (hv₀b.le.trans hbB)).trans hB)
        ((ENNReal.coe_le_coe.2 hcA).trans hA) hqq.symm (hqq ▸ hqH) (fun v hv => ?_)
        (fun s t hs ht hst => ?_) hbar₂
      · exact hinβ v ⟨hv.1, hv.2.trans_lt hv₀b⟩
      · exact hnc t s (ht.le.trans hcA) ((hs.trans hv₀b).le.trans hbB) hst.symm ht (hs.trans hv₀b)
    -- a real corner: `(d, c)` is the first contact of `β|[0, d']` and `α|[0, c]`
    obtain ⟨d', hdd', hd'b⟩ := exists_between hdb
    have hd'ζ : (d' : ℝ≥0∞) ≤ ζ₂ := (ENNReal.coe_le_coe.2 (hd'b.le.trans hbB)).trans hB
    have hcζ : (c : ℝ≥0∞) ≤ ζ₁ := (ENNReal.coe_le_coe.2 hcA).trans hA
    have hfc' : IsFirstContact β d' α c d c := by
      refine ⟨ENNReal.coe_le_coe.2 hdd'.le, le_rfl, hqq.symm, fun t s ht hs hts => ?_⟩
      have ht' : t ≤ d' := ENNReal.coe_le_coe.1 ht
      have hs' : s ≤ c := ENNReal.coe_le_coe.1 hs
      rcases eq_or_lt_of_le hs' with hsc | hsc
      · have := hβi ⟨zero_le, ht'.trans (hd'b.le.trans hbB)⟩ ⟨zero_le, hdb.le.trans hbB⟩
          (hts.trans (by rw [hsc]; exact hqq))
        exact ⟨this.ge, hsc.ge⟩
      · exact (hnc s t (hs'.trans hcA) (ht'.trans (hd'b.le.trans hbB)) hts.symm hsc (ht'.trans_lt hd'b)).elim
    have hcK : IsCompact (β '' Icc 0 d ∪ α '' Icc 0 c) :=
      (IsPathGood.isCompact_image hp₂ ((ENNReal.coe_le_coe.2 hdd'.le).trans hd'ζ)).union
        (IsPathGood.isCompact_image hp₁ hcζ)
    refine false_of_notMem_of_real (IsPathGood.mono hp₂ hd'ζ) (IsPathGood.mono hp₁ hcζ) isCompact_lowerArc
      isPreconnected_lowerArc hLim right_mem_lowerArc left_mem_lowerArc hfc' (hqq ▸ hqH) hdd' le_rfl
      (fun v hv _ hvD => ?_) (barrier_of_truncAt hd'ζ hcζ hbar₂)
    exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut _) (hinβ v ⟨hv.1, hv.2.trans_lt hd'b⟩)
      (H_diff_fillH_subset_jordanOut hcK hLim hvD)

/-- **Aux. lemma 72 at a lens with a real corner** (`RealCornerLensExclusion`). -/
theorem realCornerLensExclusion : RealCornerLensExclusion :=
  fun _ _ _ _ _ _ hp₁ hp₂ hx _ _ hA hB _ _ _ _ hab hcd hac hgap _ hbar₁ hbar₂ =>
    false_of_adjacent_minimalContacts hp₁ hp₂ hx hA hB hab hcd hac hgap hbar₁ hbar₂

/-- **Lemma 7.7** (`Supp10.Lemma77Statement`) from Aux. lemma 70 and Lemma 7.6 alone: the real-corner propositions of
`lemma77Statement_of_lemma76` are proved (`realCornerLensExclusion`, `realContactConfinement`). -/
theorem lemma77Statement_of_aux70_of_lemma76 (h70 : Aux70Statement.{u}) (h76 : Lemma76Statement.{u}) :
    Supp10.Lemma77Statement.{u} :=
  lemma77Statement_of_lemma76 h70 h76 realCornerLensExclusion realContactConfinement

/-- **Aux. lemma 72** (`Aux72Statement`, no two adjacent minimal contacts at any integer truncation, almost surely)
from Lemma 7.6 alone, every corner included. -/
theorem aux72Statement_of_lemma76 (h76 : Lemma76Statement.{u}) : Aux72Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ m
  have hg₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hg₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  filter_upwards [hg₁, hg₂, ae_barrier_of_lemma76 h76 hκ hκ4 hb hx hθ hh hη₁ hη₂] with ω hp₁ hp₂ hω
  exact noAdjacentMinimalContacts_of_barrier realCornerLensExclusion hp₁ hp₂ hx (coe_truncTime_le _ m)
    (coe_truncTime_le _ m) hω.1 hω.2

/-- The common first contact input of Theorem 1.5 (`Theorem15.W8FirstContactStatement`) from Aux. lemma 70 and
Lemma 7.6. -/
theorem w8FirstContactStatement_of_aux70_of_lemma76 (h70 : Aux70Statement.{u}) (h76 : Lemma76Statement.{u}) :
    Theorem15.W8FirstContactStatement.{u} :=
  Supp10.w8FirstContactStatement_of_lemma77 (lemma77Statement_of_aux70_of_lemma76 h70 h76)

end Sec7

end InteractingSLE
