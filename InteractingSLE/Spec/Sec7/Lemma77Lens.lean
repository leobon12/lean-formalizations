/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77Conf

/-!
# Lemma 7.7: no minimal lens with interior corners (Aux. lemmas 71–72)

Packet PROVE-LEMMA77 (specification §7.2, Aux. lemmas 71–72, pp. 276–279, `source/spec/p241-288.md#aux-71`).

Two adjacent minimal contacts `p = α(a) = β(b)`, `q = α(c) = β(d)` (`a < c`, `d < b`) bound a lens: the arcs
`A_w = α([a, c])` and `A_v = β([d, b])` from `p` to `q`. With the third arc `A_u = α([0, a])⁻¹ · ℓ · β([0, d])` through
the lower closing arc `ℓ` they form a θ-curve. The θ-curve theorem (`Foundations.ThetaCurve`) puts one open arc inside
the Jordan curve of the other two:

* `A_w°` inside `α([0, a]) ∪ β([0, b]) ∪ L`: the first lens side is on the left, so `β` arrives at `p` from the
  right side of `α` — Aux. lemma 71's first alternative;
* `A_v°` inside `α([0, c]) ∪ β([0, d]) ∪ L`: Aux. lemma 71's reflected alternative, `α` arriving at `q` from the
  left side of `β`;
* `A_u°` inside the lens: impossible, since `ℓ` dips into the lower half-plane and the lens is in `ℍ̄`.

This replaces the hydrodynamic chart of Aux. lemma 71's printed proof by the specification's own orientation
convention for sides (Aux. lemma 69). In each alternative the forbidden-side witness (`false_of_inside`) contradicts
Lemma 7.6 at a rational pair of stops — Aux. lemma 72 — when the arrival corner (`p`, resp. `q`) is a point of `ℍ`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open Restart Foundations.ThetaCurve

/-! ### Arc helpers -/

section ArcHelpers

variable {γ u v : ℝ → ℂ} {p q r : ℂ}

theorem isArcFrom_arcRev (h : IsArcFrom γ p q) : IsArcFrom (Sec6.arcRev γ) q p :=
  ⟨Sec6.continuousOn_arcRev h.1, Sec6.injOn_arcRev h.2.1, by rw [Sec6.arcRev_zero, h.2.2.2],
    by rw [Sec6.arcRev_one, h.2.2.1]⟩

theorem arc_arcRev : arc (Sec6.arcRev γ) = arc γ := Sec6.image_arcRev

theorem isArcFrom_arcJoin (hu : IsArcFrom u p q) (hv : IsArcFrom v q r) (hint : arc u ∩ arc v ⊆ {q}) :
    IsArcFrom (Sec6.arcJoin u v) p r := by
  have huv : u 1 = v 0 := hu.2.2.2.trans hv.2.2.1.symm
  refine ⟨Sec6.continuousOn_arcJoin hu.1 hv.1 huv, Sec6.injOn_arcJoin hu.2.1 hv.2.1 huv ?_, ?_, ?_⟩
  · rw [hu.2.2.2]; exact hint
  · rw [Sec6.arcJoin_zero, hu.2.2.1]
  · rw [Sec6.arcJoin_one, hv.2.2.2]

theorem arc_arcJoin (hu : IsArcFrom u p q) (hv : IsArcFrom v q r) :
    arc (Sec6.arcJoin u v) = arc u ∪ arc v :=
  Sec6.image_arcJoin (hu.2.2.2.trans hv.2.2.1.symm)

/-- A path on `ℝ≥0` parameters, restricted to `[s₁, s₂]` and rescaled to `[0, 1]`. -/
def segArc (η : ℝ≥0 → ℂ) (s₁ s₂ : ℝ≥0) : ℝ → ℂ := fun x => η (segParam s₁ s₂ x)

theorem isArcFrom_segArc {η : ℝ≥0 → ℂ} {s₁ s₂ : ℝ≥0} (hs : s₁ < s₂) (hc : ContinuousOn η (Icc s₁ s₂))
    (hi : InjOn η (Icc s₁ s₂)) : IsArcFrom (segArc η s₁ s₂) (η s₁) (η s₂) := by
  have hmaps : MapsTo (segParam s₁ s₂) (Icc 0 1) (Icc s₁ s₂) := fun x hx =>
    segParam_mem_Icc hs.le hx
  refine ⟨hc.comp (continuous_segParam s₁ s₂).continuousOn hmaps,
    hi.comp (injOn_segParam hs) hmaps, ?_, ?_⟩
  · simp only [segArc, segParam_zero]
  · simp only [segArc, segParam_one]

theorem arc_segArc {η : ℝ≥0 → ℂ} {s₁ s₂ : ℝ≥0} (hs : s₁ ≤ s₂) : arc (segArc η s₁ s₂) = η '' Icc s₁ s₂ := by
  show (fun x => η (segParam s₁ s₂ x)) '' Icc 0 1 = _
  rw [← image_image η (segParam s₁ s₂), image_segParam hs]

theorem mem_arcInt_segArc {η : ℝ≥0 → ℂ} {s₁ s₂ : ℝ≥0} (hs : s₁ < s₂) {v : ℝ≥0} (hv : v ∈ Ioo s₁ s₂) :
    η v ∈ arcInt (segArc η s₁ s₂) := by
  have hd : (0 : ℝ) < (s₂ : ℝ) - s₁ := sub_pos.2 hs
  have h1 : (s₁ : ℝ) < v := hv.1
  have h2 : (v : ℝ) < s₂ := hv.2
  refine ⟨((v : ℝ) - s₁) / ((s₂ : ℝ) - s₁), ⟨div_pos (by linarith) hd, (div_lt_one hd).2 (by linarith)⟩, ?_⟩
  show η (segParam s₁ s₂ _) = η v
  congr 1
  apply NNReal.eq
  rw [coe_segParam hs.le ⟨(div_pos (by linarith) hd).le, ((div_lt_one hd).2 (by linarith)).le⟩]
  field_simp
  ring

end ArcHelpers

/-! ### Inside a minimal lens -/

section Lens

variable {α β : ℝ≥0 → ℂ} {A B : ℝ≥0} {a b c d : ℝ≥0}

/-- **No contact strictly inside the lens corner**: between adjacent minimal contacts `(a, b)`, `(c, d)`
(`a < c`), there is no contact `(s, t)` with `s < c` and `t < b`. -/
theorem lens_no_contact (hβi : InjOn β (Icc 0 B)) (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hab : (a, b) ∈ Sec7.minimalContacts α A β B)
    (hgap : ∀ p ∈ Sec7.minimalContacts α A β B, p.1 ∉ Ioo a c) {s t : ℝ≥0} (hs : s ≤ A) (ht : t ≤ B)
    (hst : α s = β t) (hsc : s < c) (htb : t < b) : False := by
  obtain ⟨r, hr, hr1, hr2⟩ := exists_mem_minimalContacts_le hα hβ (show (s, t) ∈ contactSet α A β B from
    ⟨⟨zero_le, hs⟩, ⟨zero_le, ht⟩, hst⟩)
  rcases lt_trichotomy r.1 a with h | h | h
  · have := snd_lt_of_mem_minimalContacts hr hab h
    exact absurd (hr2.trans_lt htb) (not_lt.2 this.le)
  · have := eq_of_mem_contactSet_of_fst_eq hβi hr.1 hab.1 h
    rw [this] at hr2
    exact absurd htb (not_lt.2 hr2)
  · exact hgap r hr ⟨h, hr1.trans_lt hsc⟩

end Lens

/-! ### The θ-curve of a minimal lens -/

/-- **Aux. lemma 72 at interior corners.** Two good paths from `x₁ > x₂` cannot have two adjacent minimal contacts
`p = α(a) = β(b)`, `q = α(c) = β(d)` with `p, q ∈ ℍ`, if Lemma 7.6's conclusion holds (both halves) at every pair of
rational stops. -/
theorem false_of_adjacent_minimalContacts_of_mem_H {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}
    (hp₁ : IsPathGood α ζ₁ x₁) (hp₂ : IsPathGood β ζ₂ x₂) (hx : x₂ < x₁) {A B : ℝ≥0}
    (hA : (A : ℝ≥0∞) ≤ ζ₁) (hB : (B : ℝ≥0∞) ≤ ζ₂) {a b c d : ℝ≥0}
    (hab : (a, b) ∈ Sec7.minimalContacts α A β B) (hcd : (c, d) ∈ Sec7.minimalContacts α A β B)
    (hac : a < c) (hgap : ∀ p ∈ Sec7.minimalContacts α A β B, p.1 ∉ Ioo a c)
    (hpH : α a ∈ H) (hqH : α c ∈ H)
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
  have ha0 : 0 < a := pos_iff_ne_zero.2 (ne_zero_of_mem_H hp₁ hpH)
  have hd0 : 0 < d := pos_iff_ne_zero.2 (ne_zero_of_mem_H hp₂ (hqq ▸ hqH))
  have hx₁ : α 0 = x₁ := IsPathGood.zero hp₁
  have hx₂ : β 0 = x₂ := IsPathGood.zero hp₂
  have hsep := adjacent_minimalContacts hα hβ hab hcd hac hgap
  have hnc : ∀ s t : ℝ≥0, s ≤ A → t ≤ B → α s = β t → s < c → t < b → False := fun s t hs ht hst hsc htb =>
    lens_no_contact hβi hα hβ hab hgap hs ht hst hsc htb
  -- membership helpers
  have hαA : ∀ s ∈ Icc (0 : ℝ≥0) c, s ≤ A := fun s hs => hs.2.trans hcA
  have hβB : ∀ t ∈ Icc (0 : ℝ≥0) b, t ≤ B := fun t ht => ht.2.trans hbB
  -- real points of the closing arc
  set L := lowerArc x₂ x₁ with hL
  have hLre : ∀ z ∈ L, 0 ≤ z.im → z = x₁ ∨ z = x₂ := fun z hz hz0 =>
    (im_le_zero_of_mem_lowerArc hz).2 (le_antisymm (im_le_zero_of_mem_lowerArc hz).1 hz0)
  have him₁ : ∀ s ∈ Icc (0 : ℝ≥0) c, 0 ≤ (α s).im := fun s hs =>
    IsPathGood.im_nonneg hp₁ ((ENNReal.coe_le_coe.2 (hαA s hs)).trans hA)
  have him₂ : ∀ t ∈ Icc (0 : ℝ≥0) b, 0 ≤ (β t).im := fun t ht =>
    IsPathGood.im_nonneg hp₂ ((ENNReal.coe_le_coe.2 (hβB t ht)).trans hB)
  -- the five arcs
  set wA := segArc α a c with hwA
  set vA := Sec6.arcRev (segArc β d b) with hvA
  set αR := Sec6.arcRev (segArc α 0 a) with hαR
  set βF := segArc β 0 d with hβF
  set ℓ := lowerArcPath x₂ x₁ with hℓ
  have hcα : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ c → ContinuousOn α (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hα.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hcA)⟩ : s ∈ Icc 0 A)
  have hiα : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ c → InjOn α (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hαi.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hcA)⟩ : s ∈ Icc 0 A)
  have hcβ : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ b → ContinuousOn β (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hβ.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hbB)⟩ : s ∈ Icc 0 B)
  have hiβ : ∀ {s₁ s₂ : ℝ≥0}, s₂ ≤ b → InjOn β (Icc s₁ s₂) := fun {s₁ s₂} h =>
    hβi.mono fun s (hs : s ∈ Icc s₁ s₂) => (⟨zero_le, hs.2.trans (h.trans hbB)⟩ : s ∈ Icc 0 B)
  have hw : IsArcFrom wA (α a) (α c) := isArcFrom_segArc hac (hcα le_rfl) (hiα le_rfl)
  have hv : IsArcFrom vA (α a) (α c) := by
    have := isArcFrom_arcRev (isArcFrom_segArc hdb (hcβ le_rfl) (hiβ le_rfl))
    rwa [← hpq, ← hqq] at this
  have hαRa : IsArcFrom αR (α a) (x₁ : ℂ) := by
    have := isArcFrom_arcRev (isArcFrom_segArc ha0 (hcα hac.le) (hiα hac.le))
    rwa [hx₁] at this
  have hβFa : IsArcFrom βF (x₂ : ℂ) (α c) := by
    have := isArcFrom_segArc hd0 (hcβ hdb.le) (hiβ hdb.le)
    rwa [hx₂, ← hqq] at this
  have hℓa : IsArcFrom ℓ (x₁ : ℂ) (x₂ : ℂ) := isArcFrom_lowerArcPath hx
  have harcw : arc wA = α '' Icc a c := arc_segArc hac.le
  have harcv : arc vA = β '' Icc d b := by rw [hvA, arc_arcRev, arc_segArc hdb.le]
  have harcαR : arc αR = α '' Icc 0 a := by rw [hαR, arc_arcRev, arc_segArc zero_le]
  have harcβF : arc βF = β '' Icc 0 d := arc_segArc zero_le
  have harcℓ : arc ℓ = L := rfl
  -- contacts with the seeds
  have hx₂α : ∀ s ∈ Icc (0 : ℝ≥0) c, α s = x₂ → s = c := fun s hs h => by
    by_contra hne
    exact hnc s 0 (hαA s hs) zero_le (by rw [h, hx₂]) (lt_of_le_of_ne hs.2 hne) (zero_le.trans_lt hdb)
  have hx₁β : ∀ t ∈ Icc (0 : ℝ≥0) b, β t = x₁ → t = b := fun t ht h => by
    by_contra hne
    exact hnc 0 t zero_le (hβB t ht) (by rw [h, hx₁]) (ha0.trans hac) (lt_of_le_of_ne ht.2 hne)
  -- the third arc
  have hint₁ : arc αR ∩ arc ℓ ⊆ {(x₁ : ℂ)} := by
    rintro z ⟨hz₁, hz₂⟩
    rw [harcαR] at hz₁
    obtain ⟨s, hs, rfl⟩ := hz₁
    have hsc : s ∈ Icc (0 : ℝ≥0) c := ⟨hs.1, hs.2.trans hac.le⟩
    rcases hLre _ hz₂ (him₁ s hsc) with h | h
    · exact h
    · exact absurd (hx₂α s hsc h ▸ hs.2) (not_le.2 hac)
  have hinner : IsArcFrom (Sec6.arcJoin αR ℓ) (α a) (x₂ : ℂ) := isArcFrom_arcJoin hαRa hℓa hint₁
  have harcinner : arc (Sec6.arcJoin αR ℓ) = α '' Icc 0 a ∪ L := by
    rw [arc_arcJoin hαRa hℓa, harcαR]; rfl
  have hint₂ : arc (Sec6.arcJoin αR ℓ) ∩ arc βF ⊆ {(x₂ : ℂ)} := by
    rintro z ⟨hz₁, hz₂⟩
    rw [harcinner] at hz₁
    rw [harcβF] at hz₂
    obtain ⟨t, ht, rfl⟩ := hz₂
    rcases hz₁ with ⟨s, hs, hst⟩ | hz₁
    · exact (Set.disjoint_left.1 hsep.2.1 ⟨s, hs, hst⟩ ⟨t, ht, rfl⟩).elim
    · have htb : t ∈ Icc (0 : ℝ≥0) b := ⟨ht.1, ht.2.trans hdb.le⟩
      rcases hLre _ hz₁ (him₂ t htb) with h | h
      · exact absurd (hx₁β t htb h ▸ ht.2) (not_le.2 hdb)
      · exact h
  set uA := Sec6.arcJoin (Sec6.arcJoin αR ℓ) βF with huA
  have hu : IsArcFrom uA (α a) (α c) := isArcFrom_arcJoin hinner hβFa hint₂
  have harcu : arc uA = α '' Icc 0 a ∪ L ∪ β '' Icc 0 d := by
    rw [huA, arc_arcJoin hinner hβFa, harcinner, harcβF]
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
        have := hβi ⟨zero_le, hβB t htb⟩ (⟨le_rfl, zero_le⟩ : (0 : ℝ≥0) ∈ Icc 0 B) h
        exact absurd (this ▸ ht.1) (not_le.2 hd0)
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
        have := hαi ⟨zero_le, hαA s hsc⟩ (⟨le_rfl, zero_le⟩ : (0 : ℝ≥0) ∈ Icc 0 A) h
        exact absurd (this ▸ hs.1) (not_le.2 ha0)
      · rw [hx₂α s hsc h]; exact Or.inr rfl
    · have : α s ∈ β '' Icc 0 d ∩ α '' Icc a c := ⟨hz₁, ⟨s, hs, rfl⟩⟩
      rw [hsep.2.2.2] at this
      exact Or.inr this
  have hvw : arc vA ∩ arc wA ⊆ {α a, α c} := by
    rw [harcv, harcw, inter_comm, hsep.1]
  -- the θ-curve theorem
  have hLim : ∀ z ∈ L, z.im ≤ 0 := fun z hz => (im_le_zero_of_mem_lowerArc hz).1
  rcases exists_arcInt_subset_jordanIn hu hv hw huv huw hvw with hin | hin | hin
  · -- the first lens side is inside: `β` arrives at `p` from the right side of `α`
    obtain ⟨v₀, hav₀, hv₀c⟩ := exists_between hac
    have hJ : arc uA ∪ arc vA = α '' Icc 0 a ∪ β '' Icc 0 b ∪ L := by
      rw [harcu, harcv, ← Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ d) hdb.le, image_union]
      ext z; simp only [mem_union]; tauto
    refine false_of_inside hp₁ hp₂ hav₀ ((ENNReal.coe_le_coe.2 (hv₀c.le.trans hcA)).trans hA)
      ((ENNReal.coe_le_coe.2 hbB).trans hB) hpq hpH (fun v hv => ?_) (fun s t hs ht hst => ?_) hbar₁
    · rw [← hJ]
      exact hin (mem_arcInt_segArc hac ⟨hv.1, hv.2.trans_lt hv₀c⟩)
    · exact hnc s t ((hs.trans hv₀c).le.trans hcA) (ht.le.trans hbB) hst (hs.trans hv₀c) ht
  · -- the third arc inside the lens: impossible, its lower point is outside
    have hmid : uA (3 / 8) ∈ arcInt uA := ⟨3 / 8, ⟨by norm_num, by norm_num⟩, rfl⟩
    have hval : uA (3 / 8) = ℓ (1 / 2) := by
      rw [huA, show (3 / 8 : ℝ) = 3 / 8 from rfl]
      simp only [Sec6.arcJoin]
      norm_num
    have hlow : (ℓ (1 / 2)).im < 0 := by
      rw [hℓ, lowerArcPath]
      simp only [Sec6.arcJoin, Sec6.segPath]
      norm_num
    have hz := hin hmid
    rw [hval] at hz
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
    obtain ⟨v₀, hdv₀, hv₀b⟩ := exists_between hdb
    have hJ : arc uA ∪ arc wA = β '' Icc 0 d ∪ α '' Icc 0 c ∪ L := by
      rw [harcu, harcw, ← Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ a) hac.le, image_union]
      ext z; simp only [mem_union]; tauto
    refine false_of_inside hp₂ hp₁ hdv₀ ((ENNReal.coe_le_coe.2 (hv₀b.le.trans hbB)).trans hB)
      ((ENNReal.coe_le_coe.2 hcA).trans hA) hqq.symm (hqq ▸ hqH) (fun v hv => ?_)
      (fun s t hs ht hst => ?_) hbar₂
    · rw [← hJ]
      have hmem := mem_arcInt_segArc (η := β) hdb ⟨hv.1, hv.2.trans_lt hv₀b⟩
      refine hin ?_
      obtain ⟨y, hy, hyv⟩ := hmem
      exact ⟨1 - y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simp [hvA, Sec6.arcRev, hyv]⟩
    · exact hnc t s (ht.le.trans hcA) ((hs.trans hv₀b).le.trans hbB) hst.symm ht (hs.trans hv₀b)

end Sec7

end InteractingSLE
