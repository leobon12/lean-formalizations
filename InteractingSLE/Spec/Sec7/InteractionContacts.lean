/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Contacts of two simple arcs (§7.2: Aux. lemmas 68, 91 and 73)

Packet PROVE-SEC7-B (specification §7.2, `source/spec/p241-288.md` L272–L1011 and `p289-336.md` L1–L627).
The purely topological contact statements of §7.2, for curves `ℝ≥0 → X` in a Hausdorff space.

* **Aux. lemma 68** (Minimal contacts of two simple arcs, pp. 272–273): for continuous injective
  `α : [0, A] → X`, `β : [0, B] → X`, the contact relation `C = {(s, t) | α s = β t}` and its set `P` of
  coordinatewise-minimal points (`contactSet`, `minimalContacts`):
  1. `P` is compact, and nonempty when `C` is; every point of `C` dominates a point of `P`
     (`isCompact_minimalContacts`, `exists_mem_minimalContacts_le`, `minimalContacts_nonempty`);
  2. on `P` the order of first coordinates is the reverse of the order of second coordinates, and both
     projections are closed embeddings (`snd_lt_of_mem_minimalContacts`, `fst_lt_iff_snd_lt_of_mem_minimalContacts`,
     `isClosedEmbedding_fst_minimalContacts`, `isClosedEmbedding_snd_minimalContacts`);
  3. the first intersection points in the two traversal orders agree iff `P` is a singleton
     (`exists_minimalContacts_eq_singleton_iff`, `apply_eq_apply_iff_exists_minimalContacts_eq_singleton`);
  4. two adjacent minimal contacts bound two subarcs meeting only at their endpoints, with the stated
     separations (`adjacent_minimalContacts`);
  5. a nondegenerate interval in the first projection of `P` is a common subarc traversed by `β` in the
     opposite order (`exists_strictAntiOn_of_Icc_subset_fst_image`);
  and the final dichotomy (`minimalContacts_dichotomy`).
-/

set_option autoImplicit false

noncomputable section

open Set Topology Filter
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

variable {X : Type*}

/-! ### Aux. lemma 68: the contact relation and its minimal points -/

/-- The contact relation of `α|[0, A]` and `β|[0, B]` (Aux. lemma 68, p. 272):
`C = {(s, t) ∈ [0, A] × [0, B] : α(s) = β(t)}`. -/
def contactSet (α : ℝ≥0 → X) (A : ℝ≥0) (β : ℝ≥0 → X) (B : ℝ≥0) : Set (ℝ≥0 × ℝ≥0) :=
  {p | p.1 ∈ Icc 0 A ∧ p.2 ∈ Icc 0 B ∧ α p.1 = β p.2}

/-- The minimal contacts (Aux. lemma 68, p. 272): `(s, t) ∈ C` is minimal if there is no distinct
`(u, v) ∈ C` with `u ≤ s` and `v ≤ t`. -/
def minimalContacts (α : ℝ≥0 → X) (A : ℝ≥0) (β : ℝ≥0 → X) (B : ℝ≥0) : Set (ℝ≥0 × ℝ≥0) :=
  {p | p ∈ contactSet α A β B ∧ ∀ q ∈ contactSet α A β B, q.1 ≤ p.1 → q.2 ≤ p.2 → q = p}

variable {α β : ℝ≥0 → X} {A B : ℝ≥0}

theorem minimalContacts_subset : minimalContacts α A β B ⊆ contactSet α A β B :=
  fun _ hp => hp.1

theorem contactSet_eq :
    contactSet α A β B =
      (Icc 0 A ×ˢ Icc 0 B) ∩ (fun p : ℝ≥0 × ℝ≥0 => (α p.1, β p.2)) ⁻¹' diagonal X := by
  ext p
  simp only [contactSet, mem_inter_iff, mem_prod, mem_preimage, mem_diagonal_iff, and_assoc]
  rfl

/-- The contact relation is compact ("the diagonal in `X × X` is closed, so `C` is compact"). -/
theorem isCompact_contactSet [TopologicalSpace X] [T2Space X] (hα : ContinuousOn α (Icc 0 A))
    (hβ : ContinuousOn β (Icc 0 B)) : IsCompact (contactSet α A β B) := by
  rw [contactSet_eq]
  have hc : ContinuousOn (fun p : ℝ≥0 × ℝ≥0 => (α p.1, β p.2)) (Icc 0 A ×ˢ Icc 0 B) :=
    (hα.comp continuousOn_fst fun p hp => hp.1).prodMk (hβ.comp continuousOn_snd fun p hp => hp.2)
  have hK : IsCompact (Icc 0 A ×ˢ Icc 0 B) := isCompact_Icc.prod isCompact_Icc
  exact hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed isClosed_diagonal)
    inter_subset_left

/-- Injectivity of `β`: two contacts with the same first coordinate are equal. -/
theorem eq_of_mem_contactSet_of_fst_eq (hβi : InjOn β (Icc 0 B)) {p q : ℝ≥0 × ℝ≥0}
    (hp : p ∈ contactSet α A β B) (hq : q ∈ contactSet α A β B) (h : p.1 = q.1) : p = q :=
  Prod.ext h (hβi hp.2.1 hq.2.1 (by rw [← hp.2.2, ← hq.2.2, h]))

/-- Injectivity of `α`: two contacts with the same second coordinate are equal. -/
theorem eq_of_mem_contactSet_of_snd_eq (hαi : InjOn α (Icc 0 A)) {p q : ℝ≥0 × ℝ≥0}
    (hp : p ∈ contactSet α A β B) (hq : q ∈ contactSet α A β B) (h : p.2 = q.2) : p = q :=
  Prod.ext (hαi hp.1 hq.1 (by rw [hp.2.2, hq.2.2, h])) h

/-- **Aux. lemma 68 (1), domination.** Every contact dominates a minimal contact (minimize `u + v` on
the compact set of contacts below it). -/
theorem exists_mem_minimalContacts_le [TopologicalSpace X] [T2Space X] (hα : ContinuousOn α (Icc 0 A))
    (hβ : ContinuousOn β (Icc 0 B)) {p : ℝ≥0 × ℝ≥0} (hp : p ∈ contactSet α A β B) :
    ∃ q ∈ minimalContacts α A β B, q.1 ≤ p.1 ∧ q.2 ≤ p.2 := by
  set S := contactSet α A β B ∩ {q | q.1 ≤ p.1 ∧ q.2 ≤ p.2} with hS_def
  have hc₁ : IsClosed {q : ℝ≥0 × ℝ≥0 | q.1 ≤ p.1} := isClosed_le continuous_fst continuous_const
  have hc₂ : IsClosed {q : ℝ≥0 × ℝ≥0 | q.2 ≤ p.2} := isClosed_le continuous_snd continuous_const
  have hS : IsCompact S := (isCompact_contactSet hα hβ).inter_right (hc₁.inter hc₂)
  obtain ⟨q, hqS, hmin⟩ :=
    hS.exists_isMinOn ⟨p, hp, le_rfl, le_rfl⟩ (continuous_fst.add continuous_snd).continuousOn
  refine ⟨q, ⟨hqS.1, fun r hr h1 h2 => ?_⟩, hqS.2⟩
  have hrS : r ∈ S := ⟨hr, h1.trans hqS.2.1, h2.trans hqS.2.2⟩
  have hle : q.1 + q.2 ≤ r.1 + r.2 := hmin hrS
  refine Prod.ext (le_antisymm h1 ?_) (le_antisymm h2 ?_)
  · exact le_of_add_le_add_right (hle.trans (add_le_add_right h2 r.1))
  · exact le_of_add_le_add_left (hle.trans (add_le_add_left h1 r.2))

/-- **Aux. lemma 68 (1), nonemptiness.** -/
theorem minimalContacts_nonempty [TopologicalSpace X] [T2Space X] (hα : ContinuousOn α (Icc 0 A))
    (hβ : ContinuousOn β (Icc 0 B)) (hC : (contactSet α A β B).Nonempty) :
    (minimalContacts α A β B).Nonempty := by
  obtain ⟨p, hp⟩ := hC
  obtain ⟨q, hq, -⟩ := exists_mem_minimalContacts_le hα hβ hp
  exact ⟨q, hq⟩

/-- For injective arcs, minimality is the absence of a contact strictly below in both coordinates. -/
theorem minimalContacts_eq (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B)) :
    minimalContacts α A β B =
      contactSet α A β B ∩ ⋂ q ∈ contactSet α A β B, {p : ℝ≥0 × ℝ≥0 | p.1 ≤ q.1 ∨ p.2 ≤ q.2} := by
  ext p
  simp only [minimalContacts, mem_inter_iff, mem_iInter]
  refine and_congr_right fun hp => ⟨fun h q hq => ?_, fun h q hq h1 h2 => ?_⟩
  · by_contra hcon
    change ¬ (p.1 ≤ q.1 ∨ p.2 ≤ q.2) at hcon
    rw [not_or, not_le, not_le] at hcon
    have := h q hq hcon.1.le hcon.2.le
    rw [this] at hcon
    exact lt_irrefl _ hcon.1
  · rcases h q hq with h' | h'
    · exact eq_of_mem_contactSet_of_fst_eq hβi hq hp (le_antisymm h1 h')
    · exact eq_of_mem_contactSet_of_snd_eq hαi hq hp (le_antisymm h2 h')

/-- **Aux. lemma 68 (1), compactness.** The set of minimal contacts is compact. -/
theorem isCompact_minimalContacts [TopologicalSpace X] [T2Space X] (hα : ContinuousOn α (Icc 0 A))
    (hβ : ContinuousOn β (Icc 0 B)) (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B)) :
    IsCompact (minimalContacts α A β B) := by
  rw [minimalContacts_eq hαi hβi]
  refine (isCompact_contactSet hα hβ).inter_right (isClosed_biInter fun q _ => ?_)
  have hc₁ : IsClosed {p : ℝ≥0 × ℝ≥0 | p.1 ≤ q.1} := isClosed_le continuous_fst continuous_const
  have hc₂ : IsClosed {p : ℝ≥0 × ℝ≥0 | p.2 ≤ q.2} := isClosed_le continuous_snd continuous_const
  exact hc₁.union hc₂

/-- **Aux. lemma 68 (2).** If `(a, b), (c, d) ∈ P` and `a < c`, then `b > d`. -/
theorem snd_lt_of_mem_minimalContacts {p q : ℝ≥0 × ℝ≥0} (hp : p ∈ minimalContacts α A β B)
    (hq : q ∈ minimalContacts α A β B) (h : p.1 < q.1) : q.2 < p.2 := by
  by_contra h'
  rw [not_lt] at h'
  have := hq.2 p hp.1 h.le h'
  rw [this] at h
  exact lt_irrefl _ h

/-- **Aux. lemma 68 (2).** On `P`, the correspondence between the two coordinates is strictly
decreasing. -/
theorem fst_lt_iff_snd_lt_of_mem_minimalContacts {p q : ℝ≥0 × ℝ≥0}
    (hp : p ∈ minimalContacts α A β B) (hq : q ∈ minimalContacts α A β B) :
    p.1 < q.1 ↔ q.2 < p.2 := by
  refine ⟨snd_lt_of_mem_minimalContacts hp hq, fun h => ?_⟩
  by_contra h'
  rw [not_lt] at h'
  have := hp.2 q hq.1 h' h.le
  rw [this] at h
  exact lt_irrefl _ h

/-- **Aux. lemma 68 (2).** The first-coordinate projection of `P` is a homeomorphism onto its image
(a closed embedding: a continuous injection of a compact space into a Hausdorff space). -/
theorem isClosedEmbedding_fst_minimalContacts [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B)) (hαi : InjOn α (Icc 0 A))
    (hβi : InjOn β (Icc 0 B)) :
    IsClosedEmbedding fun p : minimalContacts α A β B => (p : ℝ≥0 × ℝ≥0).1 := by
  have : CompactSpace (minimalContacts α A β B) :=
    isCompact_iff_compactSpace.mp (isCompact_minimalContacts hα hβ hαi hβi)
  exact (continuous_fst.comp continuous_subtype_val).isClosedEmbedding fun p q h =>
    Subtype.ext (eq_of_mem_contactSet_of_fst_eq hβi p.2.1 q.2.1 h)

/-- **Aux. lemma 68 (2).** The second-coordinate projection of `P` is a homeomorphism onto its
image. -/
theorem isClosedEmbedding_snd_minimalContacts [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B)) (hαi : InjOn α (Icc 0 A))
    (hβi : InjOn β (Icc 0 B)) :
    IsClosedEmbedding fun p : minimalContacts α A β B => (p : ℝ≥0 × ℝ≥0).2 := by
  have : CompactSpace (minimalContacts α A β B) :=
    isCompact_iff_compactSpace.mp (isCompact_minimalContacts hα hβ hαi hβi)
  exact (continuous_snd.comp continuous_subtype_val).isClosedEmbedding fun p q h =>
    Subtype.ext (eq_of_mem_contactSet_of_snd_eq hαi p.2.1 q.2.1 h)

/-- The least first coordinate of the contact relation is attained (compactness). -/
theorem exists_mem_contactSet_forall_fst_le [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hC : (contactSet α A β B).Nonempty) :
    ∃ p ∈ contactSet α A β B, ∀ q ∈ contactSet α A β B, p.1 ≤ q.1 := by
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_contactSet hα hβ).exists_isMinOn hC continuous_fst.continuousOn
  exact ⟨p, hp, fun q hq => hmin hq⟩

/-- The least second coordinate of the contact relation is attained (compactness). -/
theorem exists_mem_contactSet_forall_snd_le [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hC : (contactSet α A β B).Nonempty) :
    ∃ p ∈ contactSet α A β B, ∀ q ∈ contactSet α A β B, p.2 ≤ q.2 := by
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_contactSet hα hβ).exists_isMinOn hC continuous_snd.continuousOn
  exact ⟨p, hp, fun q hq => hmin hq⟩

/-- **Aux. lemma 68 (3)**, order form: `P` is a singleton iff the contact relation has a
coordinatewise least element. -/
theorem exists_minimalContacts_eq_singleton_iff [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B)) :
    (∃ p, minimalContacts α A β B = {p}) ↔
      ∃ p ∈ contactSet α A β B, ∀ q ∈ contactSet α A β B, p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
  constructor
  · rintro ⟨p, hP⟩
    have hp : p ∈ minimalContacts α A β B := hP ▸ mem_singleton p
    refine ⟨p, hp.1, fun q hq => ?_⟩
    obtain ⟨r, hr, h1, h2⟩ := exists_mem_minimalContacts_le hα hβ hq
    rw [hP, mem_singleton_iff] at hr
    exact hr ▸ ⟨h1, h2⟩
  · rintro ⟨p, hp, hle⟩
    refine ⟨p, Subset.antisymm (fun r hr => ?_) (singleton_subset_iff.mpr ⟨hp, fun q hq h1 h2 =>
      Prod.ext (le_antisymm h1 (hle q hq).1) (le_antisymm h2 (hle q hq).2)⟩)⟩
    exact mem_singleton_iff.mpr (hr.2 p hp (hle r hr.1).1 (hle r hr.1).2).symm

/-- **Aux. lemma 68 (3).** The first intersection points seen in the two traversal orders — `α(s₁)`
with `s₁` the least first coordinate of a contact and `β(t₂)` with `t₂` the least second
coordinate — agree iff `P` consists of one point. -/
theorem apply_eq_apply_iff_exists_minimalContacts_eq_singleton [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B)) (hαi : InjOn α (Icc 0 A))
    (hβi : InjOn β (Icc 0 B)) {s₁ t₁ s₂ t₂ : ℝ≥0} (h₁ : (s₁, t₁) ∈ contactSet α A β B)
    (h₁min : ∀ q ∈ contactSet α A β B, s₁ ≤ q.1) (h₂ : (s₂, t₂) ∈ contactSet α A β B)
    (h₂min : ∀ q ∈ contactSet α A β B, t₂ ≤ q.2) :
    α s₁ = β t₂ ↔ ∃ p, minimalContacts α A β B = {p} := by
  rw [exists_minimalContacts_eq_singleton_iff hα hβ]
  constructor
  · intro h
    exact ⟨(s₁, t₂), ⟨h₁.1, h₂.2.1, h⟩, fun q hq => ⟨h₁min q hq, h₂min q hq⟩⟩
  · rintro ⟨p, hp, hle⟩
    have e₁ : (s₁, t₁) = p :=
      eq_of_mem_contactSet_of_fst_eq hβi h₁ hp (le_antisymm (h₁min p hp) (hle _ h₁).1)
    have e₂ : (s₂, t₂) = p :=
      eq_of_mem_contactSet_of_snd_eq hαi h₂ hp (le_antisymm (h₂min p hp) (hle _ h₂).2)
    have ht : t₁ = t₂ := (congrArg Prod.snd e₁).trans (congrArg Prod.snd e₂).symm
    rw [← ht]
    exact h₁.2.2

/-- **Aux. lemma 68 (4).** Let `(a, b), (c, d) ∈ P` with `a < c` and no point of the first projection
of `P` in `(a, c)`. Then `α([a, c]) ∩ β([d, b]) = {α(a), α(c)}`; `α([0, a])` and `β([0, d])` are
disjoint; `α([0, a])` meets `β([d, b])` only at `α(a)`; and `β([0, d])` meets `α([a, c])` only at
`α(c)`. -/
theorem adjacent_minimalContacts [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    {a b c d : ℝ≥0} (hab : (a, b) ∈ minimalContacts α A β B)
    (hcd : (c, d) ∈ minimalContacts α A β B) (hac : a < c)
    (hgap : ∀ p ∈ minimalContacts α A β B, p.1 ∉ Ioo a c) :
    α '' Icc a c ∩ β '' Icc d b = {α a, α c} ∧ Disjoint (α '' Icc 0 a) (β '' Icc 0 d) ∧
      α '' Icc 0 a ∩ β '' Icc d b = {α a} ∧ β '' Icc 0 d ∩ α '' Icc a c = {α c} := by
  have hdb : d < b := snd_lt_of_mem_minimalContacts hab hcd hac
  have hab' := hab.1
  have hcd' := hcd.1
  refine ⟨Subset.antisymm ?_ ?_, ?_, Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_⟩
  · rintro z ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    have huv : (u, v) ∈ contactSet α A β B :=
      ⟨⟨zero_le, hu.2.trans hcd'.1.2⟩, ⟨zero_le, hv.2.trans hab'.2.1.2⟩, hvu.symm⟩
    by_contra hz
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
    have huc : u < c := lt_of_le_of_ne hu.2 fun h => hz.2 (by rw [h])
    have hvb : v < b := lt_of_le_of_ne hv.2 fun h => hz.1 (by rw [← hvu, h, ← hab'.2.2])
    obtain ⟨r, hr, hr1, hr2⟩ := exists_mem_minimalContacts_le hα hβ huv
    have h1 : a < r.1 := by
      by_contra h
      rw [not_lt] at h
      have := hab.2 r hr.1 h (hr2.trans hvb.le)
      rw [this] at hr2
      exact absurd hr2 (not_le.mpr hvb)
    exact hgap r hr ⟨h1, hr1.trans_lt huc⟩
  · rintro z (rfl | rfl)
    · exact ⟨⟨a, ⟨le_rfl, hac.le⟩, rfl⟩, ⟨b, ⟨hdb.le, le_rfl⟩, hab'.2.2.symm⟩⟩
    · exact ⟨⟨c, ⟨hac.le, le_rfl⟩, rfl⟩, ⟨d, ⟨le_rfl, hdb.le⟩, hcd'.2.2.symm⟩⟩
  · rw [Set.disjoint_left]
    rintro z ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have huv : (u, v) ∈ contactSet α A β B :=
      ⟨⟨zero_le, hu.2.trans hab'.1.2⟩, ⟨zero_le, hv.2.trans hcd'.2.1.2⟩, hvu.symm⟩
    have hvb : v = b := congrArg Prod.snd (hab.2 (u, v) huv hu.2 (hv.2.trans hdb.le))
    exact absurd (hvb ▸ hv.2) (not_le.mpr hdb)
  · rintro z ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    have huv : (u, v) ∈ contactSet α A β B :=
      ⟨⟨zero_le, hu.2.trans hab'.1.2⟩, ⟨zero_le, hv.2.trans hab'.2.1.2⟩, hvu.symm⟩
    have hu' : u = a := congrArg Prod.fst (hab.2 (u, v) huv hu.2 hv.2)
    rw [mem_singleton_iff, hu']
  · rintro z rfl
    exact ⟨⟨a, ⟨zero_le, le_rfl⟩, rfl⟩, ⟨b, ⟨hdb.le, le_rfl⟩, hab'.2.2.symm⟩⟩
  · rintro z ⟨⟨v, hv, rfl⟩, ⟨u, hu, huv⟩⟩
    have hc : (u, v) ∈ contactSet α A β B :=
      ⟨⟨zero_le, hu.2.trans hcd'.1.2⟩, ⟨zero_le, hv.2.trans hcd'.2.1.2⟩, huv⟩
    have hu' : u = c := congrArg Prod.fst (hcd.2 (u, v) hc hu.2 hv.2)
    rw [mem_singleton_iff, ← huv, hu']
  · rintro z rfl
    exact ⟨⟨d, ⟨zero_le, le_rfl⟩, hcd'.2.2.symm⟩, ⟨c, ⟨hac.le, le_rfl⟩, rfl⟩⟩

/-- **Aux. lemma 68 (5).** If the first-coordinate projection of `P` contains the interval `[a, c]`,
then `α([a, c])` is a common subarc traversed by `β` in the opposite order: there is a continuous
strictly decreasing `f` on `[a, c]` with `(s, f s) ∈ P` (so `β(f s) = α(s)`), mapping `[a, c]` onto
`[f c, f a]`, and `β([f c, f a]) = α([a, c])`. -/
theorem exists_strictAntiOn_of_Icc_subset_fst_image [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B)) (hαi : InjOn α (Icc 0 A))
    (hβi : InjOn β (Icc 0 B)) {a c : ℝ≥0} (hac : a ≤ c)
    (hsub : Icc a c ⊆ Prod.fst '' minimalContacts α A β B) :
    ∃ f : ℝ≥0 → ℝ≥0, ContinuousOn f (Icc a c) ∧ StrictAntiOn f (Icc a c) ∧
      f '' Icc a c = Icc (f c) (f a) ∧ (∀ s ∈ Icc a c, (s, f s) ∈ minimalContacts α A β B) ∧
      (∀ s ∈ Icc a c, β (f s) = α s) ∧ β '' Icc (f c) (f a) = α '' Icc a c := by
  classical
  let f : ℝ≥0 → ℝ≥0 := fun s =>
    if h : ∃ p ∈ minimalContacts α A β B, p.1 = s then h.choose.2 else 0
  have hfP : ∀ s ∈ Icc a c, (s, f s) ∈ minimalContacts α A β B := by
    intro s hs
    have h : ∃ p ∈ minimalContacts α A β B, p.1 = s := hsub hs
    have hf : f s = h.choose.2 := dite_eq_left h
    have : (s, f s) = h.choose := by
      rw [hf]
      exact Prod.ext h.choose_spec.2.symm rfl
    rw [this]
    exact h.choose_spec.1
  have hanti : StrictAntiOn f (Icc a c) := fun s hs s' hs' hss' =>
    snd_lt_of_mem_minimalContacts (hfP s hs) (hfP s' hs') hss'
  have hcont : ContinuousOn f (Icc a c) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let k : Icc a c → minimalContacts α A β B := fun s => ⟨(s, f s), hfP s s.2⟩
    have hk : Continuous k := by
      rw [(isClosedEmbedding_fst_minimalContacts hα hβ hαi hβi).isInducing.continuous_iff]
      exact continuous_subtype_val
    exact continuous_snd.comp (continuous_subtype_val.comp hk)
  have himg : f '' Icc a c = Icc (f c) (f a) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨hanti.antitoneOn hs ⟨hac, le_rfl⟩ hs.2, hanti.antitoneOn ⟨le_rfl, hac⟩ hs hs.1⟩
    · exact (isPreconnected_Icc.image f hcont).Icc_subset ⟨c, ⟨hac, le_rfl⟩, rfl⟩
        ⟨a, ⟨le_rfl, hac⟩, rfl⟩
  have heq : ∀ s ∈ Icc a c, β (f s) = α s := fun s hs => (hfP s hs).1.2.2.symm
  refine ⟨f, hcont, hanti, himg, hfP, heq, ?_⟩
  rw [← himg, image_image]
  exact image_congr heq

/-- **Aux. lemma 68**, final dichotomy: if the two first intersection points differ (`P` is not a
singleton), then either the first projection of `P` contains a nondegenerate interval (an oppositely
traversed common subarc, part 5) or there are two adjacent minimal contacts as in part 4. -/
theorem minimalContacts_dichotomy [TopologicalSpace X] [T2Space X]
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B)) (hαi : InjOn α (Icc 0 A))
    (hβi : InjOn β (Icc 0 B)) (hC : (contactSet α A β B).Nonempty)
    (hP : ¬ ∃ p, minimalContacts α A β B = {p}) :
    (∃ a c : ℝ≥0, a < c ∧ Icc a c ⊆ Prod.fst '' minimalContacts α A β B) ∨
      ∃ a b c d : ℝ≥0, (a, b) ∈ minimalContacts α A β B ∧ (c, d) ∈ minimalContacts α A β B ∧
        a < c ∧ ∀ p ∈ minimalContacts α A β B, p.1 ∉ Ioo a c := by
  have hSc : IsCompact (Prod.fst '' minimalContacts α A β B) :=
    (isCompact_minimalContacts hα hβ hαi hβi).image continuous_fst
  have hSne : (Prod.fst '' minimalContacts α A β B).Nonempty :=
    (minimalContacts_nonempty hα hβ hC).image _
  obtain ⟨m, hmS, hm⟩ := hSc.exists_isLeast hSne
  obtain ⟨M, hMS, hM⟩ := hSc.exists_isGreatest hSne
  have hmM : m < M := by
    rcases (hm hMS).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hP
      obtain ⟨p, hp, rfl⟩ := hmS
      refine ⟨p, Subset.antisymm (fun q hq => ?_) (singleton_subset_iff.mpr hp)⟩
      have h1 : p.1 ≤ q.1 := hm ⟨q, hq, rfl⟩
      have h2 : q.1 ≤ M := hM ⟨q, hq, rfl⟩
      exact mem_singleton_iff.mpr
        (eq_of_mem_contactSet_of_fst_eq hβi hq.1 hp.1 (le_antisymm (h2.trans h.symm.le) h1))
  by_cases hI : Icc m M ⊆ Prod.fst '' minimalContacts α A β B
  · exact Or.inl ⟨m, M, hmM, hI⟩
  · right
    obtain ⟨x, hx, hxS⟩ := not_subset.mp hI
    have hmx : m < x := lt_of_le_of_ne hx.1 fun h => hxS (h ▸ hmS)
    have hxM : x < M := lt_of_le_of_ne hx.2 fun h => hxS (h.symm ▸ hMS)
    obtain ⟨a', ⟨ha'S, ha'x⟩, ha'ub⟩ :=
      (hSc.inter_right isClosed_Iic).exists_isGreatest ⟨m, hmS, hmx.le⟩
    obtain ⟨c', ⟨hc'S, hc'x⟩, hc'lb⟩ :=
      (hSc.inter_right isClosed_Ici).exists_isLeast ⟨M, hMS, hxM.le⟩
    have ha'lt : a' < x := lt_of_le_of_ne ha'x fun h => hxS (h ▸ ha'S)
    have hc'gt : x < c' := lt_of_le_of_ne hc'x fun h => hxS (h.symm ▸ hc'S)
    obtain ⟨pa, hpa, rfl⟩ := ha'S
    obtain ⟨pc, hpc, rfl⟩ := hc'S
    refine ⟨pa.1, pa.2, pc.1, pc.2, hpa, hpc, ha'lt.trans hc'gt, fun p hp hpI => ?_⟩
    rcases le_or_gt p.1 x with h | h
    · exact absurd (ha'ub ⟨⟨p, hp, rfl⟩, h⟩) (not_le.mpr hpI.1)
    · exact absurd (hc'lb ⟨⟨p, hp, rfl⟩, h.le⟩) (not_le.mpr hpI.2)

/-! ### Aux. lemmas 91 and 73: no return after a common selected contact -/

/-- **Aux. lemma 91** (The precise no-return implication for a later contact, pp. 309–310). Let
`α|[0, T₁]`, `β|[0, T₂]` be injective and `σ ≤ T₂`. Suppose the first contact of `α([0, T₁])` with
`β([σ, T₂])` in the two traversal orders is attained at one point `q = α(τ₁) = β(τ₂)` with `τ₂ ≥ σ`:
`τ₁` is the least first coordinate and `τ₂` the least second coordinate of the contacts `α(s) = β(t)`
with `σ ≤ t`. Then (NRL1): `β((τ₂, T₂]) ∩ K = ∅` with `K = α([0, τ₁]) ∪ β([0, τ₂])`, and
`α((τ₁, T₁]) ∩ (α([0, τ₁]) ∪ β([σ, τ₂])) = ∅`. Continuity is not needed. -/
theorem no_return_of_laterContact {α β : ℝ≥0 → X} {T₁ T₂ : ℝ≥0∞} {σ τ₁ τ₂ : ℝ≥0}
    (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁}) (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hτ₁ : (τ₁ : ℝ≥0∞) ≤ T₁) (hτ₂ : (τ₂ : ℝ≥0∞) ≤ T₂) (hστ : σ ≤ τ₂) (hq : α τ₁ = β τ₂)
    (hmin₁ : ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ T₁ → σ ≤ t → (t : ℝ≥0∞) ≤ T₂ → α s = β t → τ₁ ≤ s)
    (hmin₂ : ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ T₁ → σ ≤ t → (t : ℝ≥0∞) ≤ T₂ → α s = β t → τ₂ ≤ t) :
    (∀ t : ℝ≥0, τ₂ < t → (t : ℝ≥0∞) ≤ T₂ → β t ∉ α '' Icc 0 τ₁ ∪ β '' Icc 0 τ₂) ∧
      ∀ s : ℝ≥0, τ₁ < s → (s : ℝ≥0∞) ≤ T₁ → α s ∉ α '' Icc 0 τ₁ ∪ β '' Icc σ τ₂ := by
  constructor
  · rintro t ht htT (⟨u, hu, hut⟩ | ⟨v, hv, hvt⟩)
    · have huT : (u : ℝ≥0∞) ≤ T₁ := (ENNReal.coe_le_coe.mpr hu.2).trans hτ₁
      have hu' : u = τ₁ := le_antisymm hu.2 (hmin₁ u t huT (hστ.trans ht.le) htT hut)
      have : t = τ₂ := hβi htT hτ₂ (by rw [← hut, hu', hq])
      exact absurd this ht.ne'
    · have hvT : (v : ℝ≥0∞) ≤ T₂ := (ENNReal.coe_le_coe.mpr hv.2).trans hτ₂
      have : v = t := hβi hvT htT hvt
      exact absurd (this ▸ hv.2) (not_le.mpr ht)
  · rintro s hs hsT (⟨u, hu, hus⟩ | ⟨v, hv, hvs⟩)
    · have huT : (u : ℝ≥0∞) ≤ T₁ := (ENNReal.coe_le_coe.mpr hu.2).trans hτ₁
      have : u = s := hαi huT hsT hus
      exact absurd (this ▸ hu.2) (not_le.mpr hs)
    · have hvT : (v : ℝ≥0∞) ≤ T₂ := (ENNReal.coe_le_coe.mpr hv.2).trans hτ₂
      have hv' : v = τ₂ := le_antisymm hv.2 (hmin₂ s v hsT hv.1 hvT hvs.symm)
      have : s = τ₁ := hαi hsT hτ₁ (by rw [← hvs, hv', ← hq])
      exact absurd this hs.ne'

/-- **Aux. lemma 91**, consequence: in its setting, any return of the first continuation to
`K = α([0, τ₁]) ∪ β([0, τ₂])` belongs to `β([0, σ))`. -/
theorem mem_image_Ico_of_laterContact {α β : ℝ≥0 → X} {T₁ T₂ : ℝ≥0∞} {σ τ₁ τ₂ : ℝ≥0}
    (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁}) (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hτ₁ : (τ₁ : ℝ≥0∞) ≤ T₁) (hτ₂ : (τ₂ : ℝ≥0∞) ≤ T₂) (hστ : σ ≤ τ₂) (hq : α τ₁ = β τ₂)
    (hmin₁ : ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ T₁ → σ ≤ t → (t : ℝ≥0∞) ≤ T₂ → α s = β t → τ₁ ≤ s)
    (hmin₂ : ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ T₁ → σ ≤ t → (t : ℝ≥0∞) ≤ T₂ → α s = β t → τ₂ ≤ t)
    {s : ℝ≥0} (hs : τ₁ < s) (hsT : (s : ℝ≥0∞) ≤ T₁)
    (hK : α s ∈ α '' Icc 0 τ₁ ∪ β '' Icc 0 τ₂) : α s ∈ β '' Ico 0 σ := by
  have hno := (no_return_of_laterContact hαi hβi hτ₁ hτ₂ hστ hq hmin₁ hmin₂).2 s hs hsT
  rcases hK with hK | ⟨v, hv, hvs⟩
  · exact absurd (Or.inl hK) hno
  · refine ⟨v, ⟨zero_le, lt_of_not_ge fun hσv => hno (Or.inr ⟨v, ⟨hσv, hv.2⟩, hvs⟩)⟩, hvs⟩

/-- **Aux. lemma 73** (No return to the two selected prefixes, p. 279). Let `α|[0, T₁]`, `β|[0, T₂]`
be injective, and suppose their first intersection points in the two traversal orders agree at
`w = α(a) = β(b)`, i.e. `a` and `b` are the least coordinates of the contacts (the body of
`IsFirstContact`). Then `α((a, T₁])` and `β((b, T₂])` avoid `α([0, a]) ∪ β([0, b])`. -/
theorem no_return_of_firstContact {α β : ℝ≥0 → X} {T₁ T₂ : ℝ≥0∞} {a b : ℝ≥0}
    (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁}) (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (ha : (a : ℝ≥0∞) ≤ T₁) (hb : (b : ℝ≥0∞) ≤ T₂) (hw : α a = β b)
    (hmin : ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ T₁ → (t : ℝ≥0∞) ≤ T₂ → α s = β t → a ≤ s ∧ b ≤ t) :
    (∀ s : ℝ≥0, a < s → (s : ℝ≥0∞) ≤ T₁ → α s ∉ α '' Icc 0 a ∪ β '' Icc 0 b) ∧
      ∀ t : ℝ≥0, b < t → (t : ℝ≥0∞) ≤ T₂ → β t ∉ α '' Icc 0 a ∪ β '' Icc 0 b := by
  have h := no_return_of_laterContact (σ := 0) hαi hβi ha hb zero_le hw
    (fun s t hs _ ht hst => (hmin s t hs ht hst).1) (fun s t hs _ ht hst => (hmin s t hs ht hst).2)
  exact ⟨h.2, h.1⟩

/-! ### Aux. lemma 67: proper stopped curves and finite contact selection -/

/-- The finite-parameter contact relation of the stopped curves `α|[σ₁, T₁]` and `β|[σ₂, T₂]`
(Aux. lemma 67, pp. 270–271; `T_i = ∞` allowed, contacts only at finite parameters). -/
def stoppedContactSet (α : ℝ≥0 → X) (σ₁ : ℝ≥0) (T₁ : ℝ≥0∞) (β : ℝ≥0 → X) (σ₂ : ℝ≥0)
    (T₂ : ℝ≥0∞) : Set (ℝ≥0 × ℝ≥0) :=
  {p | σ₁ ≤ p.1 ∧ (p.1 : ℝ≥0∞) ≤ T₁ ∧ σ₂ ≤ p.2 ∧ (p.2 : ℝ≥0∞) ≤ T₂ ∧ α p.1 = β p.2}

theorem swap_mem_stoppedContactSet {α β : ℝ≥0 → X} {σ₁ σ₂ : ℝ≥0} {T₁ T₂ : ℝ≥0∞}
    {p : ℝ≥0 × ℝ≥0} :
    p.swap ∈ stoppedContactSet β σ₂ T₂ α σ₁ T₁ ↔ p ∈ stoppedContactSet α σ₁ T₁ β σ₂ T₂ :=
  ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h3, h4, h1, h2, h5.symm⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h3, h4, h1, h2, h5.symm⟩⟩

theorem setOf_coe_le_coe_eq_Icc (T : ℝ≥0) : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T} = Icc 0 T := by
  ext t
  exact ENNReal.coe_le_coe.trans ⟨fun h => ⟨zero_le, h⟩, fun h => h.2⟩

/-- Compactness of the contacts of two curves on parameter boxes. -/
theorem isCompact_contacts_Icc [TopologicalSpace X] [T2Space X] {α β : ℝ≥0 → X}
    {a₁ b₁ a₂ b₂ : ℝ≥0} (hα : ContinuousOn α (Icc a₁ b₁)) (hβ : ContinuousOn β (Icc a₂ b₂)) :
    IsCompact ((Icc a₁ b₁ ×ˢ Icc a₂ b₂) ∩ {p : ℝ≥0 × ℝ≥0 | α p.1 = β p.2}) := by
  have hc : ContinuousOn (fun p : ℝ≥0 × ℝ≥0 => (α p.1, β p.2)) (Icc a₁ b₁ ×ˢ Icc a₂ b₂) :=
    (hα.comp continuousOn_fst fun p hp => hp.1).prodMk (hβ.comp continuousOn_snd fun p hp => hp.2)
  have hK : IsCompact (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := isCompact_Icc.prod isCompact_Icc
  exact hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed isClosed_diagonal)
    inter_subset_left

section Proper

variable {E : Type*} [NormedAddCommGroup E]

/-- **Aux. lemma 67** (Proper stopped curves, pp. 270–271), closed range: a curve continuous on its
stopped parameter interval `{t | t ≤ T}`, with `|α(t)| → ∞` when `T = ∞`, has closed finite-parameter
range. -/
theorem isClosed_image_stopped {α : ℝ≥0 → E} {T : ℝ≥0∞}
    (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ T})
    (hT : T = ⊤ → Tendsto (fun t => ‖α t‖) atTop atTop) :
    IsClosed (α '' {t | (t : ℝ≥0∞) ≤ T}) := by
  rcases eq_or_ne T ⊤ with rfl | hT'
  · have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ :=
      eq_univ_of_forall fun t => show (t : ℝ≥0∞) ≤ ⊤ from le_top
    rw [hset, image_univ]
    rw [hset, continuousOn_univ] at hα
    refine isClosed_of_closure_subset fun z hz => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hT rfl).eventually_gt_atTop (‖z‖ + 1))
    have hsplit : range α ⊆ α '' Icc 0 N ∪ {w | ‖z‖ + 1 ≤ ‖w‖} := by
      rintro _ ⟨t, rfl⟩
      rcases le_or_gt t N with h | h
      · exact Or.inl ⟨t, ⟨zero_le, h⟩, rfl⟩
      · exact Or.inr (hN t h.le).le
    have hK : IsClosed (α '' Icc 0 N) := (isCompact_Icc.image hα).isClosed
    have hF : IsClosed {w : E | ‖z‖ + 1 ≤ ‖w‖} := isClosed_le continuous_const continuous_norm
    have hz' := closure_mono hsplit hz
    rw [(hK.union hF).closure_eq] at hz'
    rcases hz' with h | h
    · exact image_subset_range _ _ h
    · exact absurd (show ‖z‖ + 1 ≤ ‖z‖ from h) (not_le.mpr (lt_add_one _))
  · obtain ⟨T₀, rfl⟩ : ∃ T₀ : ℝ≥0, (T₀ : ℝ≥0∞) = T := ⟨T.toNNReal, ENNReal.coe_toNNReal hT'⟩
    rw [setOf_coe_le_coe_eq_Icc] at hα ⊢
    exact (isCompact_Icc.image_of_continuousOn hα).isClosed

/-- **Aux. lemma 67** (finite contact selection, pp. 270–271): if the finite-parameter ranges of the
stopped curves `α|[σ₁, T₁]` and `β|[σ₂, T₂]` meet, the least first coordinate of a contact is
attained at a finite contact. Only the second curve needs `|β(t)| → ∞` when `T₂ = ∞` (the first
curve's range through a given contact is compact). The lower endpoints `σᵢ` give the tail
versions. -/
theorem exists_mem_stoppedContactSet_forall_fst_le {α β : ℝ≥0 → E} {σ₁ σ₂ : ℝ≥0}
    {T₁ T₂ : ℝ≥0∞} (hα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hβT : T₂ = ⊤ → Tendsto (fun t => ‖β t‖) atTop atTop)
    (hne : (stoppedContactSet α σ₁ T₁ β σ₂ T₂).Nonempty) :
    ∃ p ∈ stoppedContactSet α σ₁ T₁ β σ₂ T₂,
      ∀ q ∈ stoppedContactSet α σ₁ T₁ β σ₂ T₂, p.1 ≤ q.1 := by
  obtain ⟨⟨s₁, t₁⟩, hσs₁, hs₁T, hσt₁, ht₁T, hst₁⟩ := hne
  have hIcc₁ : Icc σ₁ s₁ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T₁} := fun s hs =>
    (ENNReal.coe_le_coe.mpr hs.2).trans hs₁T
  have hK : IsCompact (α '' Icc 0 s₁) :=
    isCompact_Icc.image_of_continuousOn
      (hα.mono fun s hs => (ENNReal.coe_le_coe.mpr hs.2).trans hs₁T)
  obtain ⟨M, ht₁M, hIcc₂, hM⟩ : ∃ M : ℝ≥0, t₁ ≤ M ∧
      Icc σ₂ M ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T₂} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T₂ → β t ∈ α '' Icc 0 s₁ → t ≤ M := by
    rcases eq_or_ne T₂ ⊤ with rfl | hT₂
    · obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
      obtain ⟨N, hN⟩ := eventually_atTop.mp ((hβT rfl).eventually_gt_atTop R)
      refine ⟨max N t₁, le_max_right _ _, fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top,
        fun t _ ht => ?_⟩
      by_contra h
      exact absurd (hR _ ht) (not_le.mpr (hN t ((le_max_left _ _).trans (not_le.mp h).le)))
    · obtain ⟨T₀, rfl⟩ : ∃ T₀ : ℝ≥0, (T₀ : ℝ≥0∞) = T₂ :=
        ⟨T₂.toNNReal, ENNReal.coe_toNNReal hT₂⟩
      exact ⟨T₀, ENNReal.coe_le_coe.mp ht₁T, fun t ht => ENNReal.coe_le_coe.mpr ht.2,
        fun t ht _ => ENNReal.coe_le_coe.mp ht⟩
  have hC : IsCompact ((Icc σ₁ s₁ ×ˢ Icc σ₂ M) ∩ {p : ℝ≥0 × ℝ≥0 | α p.1 = β p.2}) :=
    isCompact_contacts_Icc (hα.mono hIcc₁) (hβ.mono hIcc₂)
  obtain ⟨p, hp, hmin⟩ := hC.exists_isMinOn
    ⟨(s₁, t₁), ⟨⟨hσs₁, le_rfl⟩, ⟨hσt₁, ht₁M⟩⟩, hst₁⟩ continuous_fst.continuousOn
  refine ⟨p, ⟨hp.1.1.1, hIcc₁ hp.1.1, hp.1.2.1, hIcc₂ hp.1.2, hp.2⟩, fun q hq => ?_⟩
  rcases le_or_gt s₁ q.1 with h | h
  · exact hp.1.1.2.trans h
  · have hqM : q.2 ≤ M := hM q.2 hq.2.2.2.1 ⟨q.1, ⟨zero_le, h.le⟩, hq.2.2.2.2⟩
    exact hmin ⟨⟨⟨hq.1, h.le⟩, ⟨hq.2.2.1, hqM⟩⟩, hq.2.2.2.2⟩

/-- **Aux. lemma 67** (finite contact selection), second coordinate: the least second coordinate
of a contact is attained, when `|α(s)| → ∞` in case `T₁ = ∞`. -/
theorem exists_mem_stoppedContactSet_forall_snd_le {α β : ℝ≥0 → E} {σ₁ σ₂ : ℝ≥0}
    {T₁ T₂ : ℝ≥0∞} (hα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hαT : T₁ = ⊤ → Tendsto (fun s => ‖α s‖) atTop atTop)
    (hne : (stoppedContactSet α σ₁ T₁ β σ₂ T₂).Nonempty) :
    ∃ p ∈ stoppedContactSet α σ₁ T₁ β σ₂ T₂,
      ∀ q ∈ stoppedContactSet α σ₁ T₁ β σ₂ T₂, p.2 ≤ q.2 := by
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨p, hp, hmin⟩ := exists_mem_stoppedContactSet_forall_fst_le hβ hα hαT
    ⟨p₀.swap, swap_mem_stoppedContactSet.mpr hp₀⟩
  exact ⟨p.swap, (swap_mem_stoppedContactSet (p := p.swap)).mp hp,
    fun q hq => hmin q.swap (swap_mem_stoppedContactSet.mpr hq)⟩

end Proper

end Sec7

end InteractingSLE
