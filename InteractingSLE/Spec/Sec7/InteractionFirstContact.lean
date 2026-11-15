/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsFirstContact
import InteractingSLE.Frozen.Spec.IsInteriorAvailableContact
import InteractingSLE.Spec.Sec7.InteractionContacts

/-!
# First contacts of two stopped curves (§7.2, deterministic part of Lemma 7.7 and Theorem 7.9B)

Packet PROVE-SEC7-B. The frozen predicate `IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀` (Theorem 7.12C, p. 542:
"their first contacts occur at one common point") says that `(s₀, t₀)` is the coordinatewise least
element of the finite-parameter contact relation of `η₁|[0, ζ₁]` and `η₂|[0, ζ₂]`
(`isFirstContact_iff`). This file connects it with the contact statements of
`InteractingSLE.Spec.Sec7.InteractionContacts`:

* uniqueness of the first contact (`IsFirstContact.unique`);
* **Aux. lemma 73** in frozen form (`IsFirstContact.no_return`);
* **Aux. lemma 68 (3)** in frozen form, for finite lifetimes: a first contact exists iff the set of
  minimal contacts is a singleton (`exists_isFirstContact_coe_iff`), and otherwise the dichotomy of
  Aux. lemma 68 holds (`exists_isFirstContact_coe_or_dichotomy`);
* **common selection from increasing contact order** (the argument of Aux. lemma 94, claim 2,
  p. 317, and of Theorem W8: "The minima in each traversal order are attained in the compact
  rectangle …; increasing order forces the two minima to be the same pair"), using the finite contact
  selection of **Aux. lemma 67** (`exists_isFirstContact_of_contact_order`);
* the reduction of "every interior available contact is the first contact" (Theorem 1.5 (iii),
  second clause) to the absence of later contacts (`isFirstContact_of_isFirstContact_of_noLater`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- `IsFirstContact` is the coordinatewise least element of the finite-parameter contact relation. -/
theorem isFirstContact_iff {s₀ t₀ : ℝ≥0} :
    IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ ↔
      (s₀, t₀) ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂ ∧
        ∀ q ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂, s₀ ≤ q.1 ∧ t₀ ≤ q.2 := by
  constructor
  · rintro ⟨hs, ht, he, hmin⟩
    exact ⟨⟨zero_le, hs, zero_le, ht, he⟩, fun q hq => hmin q.1 q.2 hq.2.1 hq.2.2.2.1 hq.2.2.2.2⟩
  · rintro ⟨⟨-, hs, -, ht, he⟩, hmin⟩
    exact ⟨hs, ht, he, fun s t hs ht hst => hmin (s, t) ⟨zero_le, hs, zero_le, ht, hst⟩⟩

/-- The first contact is unique. -/
theorem IsFirstContact.unique {s₀ t₀ s₁ t₁ : ℝ≥0} (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (h₁ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₁ t₁) : s₀ = s₁ ∧ t₀ = t₁ := by
  have a := h₀.2.2.2 s₁ t₁ h₁.1 h₁.2.1 h₁.2.2.1
  have b := h₁.2.2.2 s₀ t₀ h₀.1 h₀.2.1 h₀.2.2.1
  exact ⟨le_antisymm a.1 b.1, le_antisymm a.2 b.2⟩

/-- An interior available contact is a finite-parameter contact of the stopped curves. -/
theorem IsInteriorAvailableContact.mem_stoppedContactSet {s t : ℝ≥0}
    (h : IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t) :
    (s, t) ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂ :=
  ⟨zero_le, h.1.le, zero_le, h.2.1.le, h.2.2.1⟩

/-- A first contact precedes every interior available contact. -/
theorem IsFirstContact.le_of_isInteriorAvailableContact {s₀ t₀ s t : ℝ≥0}
    (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) (h : IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t) :
    s₀ ≤ s ∧ t₀ ≤ t :=
  h₀.2.2.2 s t h.1.le h.2.1.le h.2.2.1

/-- **Aux. lemma 73** (No return to the two selected prefixes, p. 279), frozen form: for injective
stopped curves with first contact `w = η₁(s₀) = η₂(t₀)`, neither continuation returns to
`η₁([0, s₀]) ∪ η₂([0, t₀])`. -/
theorem IsFirstContact.no_return {s₀ t₀ : ℝ≥0} (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂}) (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) :
    (∀ s : ℝ≥0, s₀ < s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∉ η₁ '' Icc 0 s₀ ∪ η₂ '' Icc 0 t₀) ∧
      ∀ t : ℝ≥0, t₀ < t → (t : ℝ≥0∞) ≤ ζ₂ → η₂ t ∉ η₁ '' Icc 0 s₀ ∪ η₂ '' Icc 0 t₀ :=
  no_return_of_firstContact hi₁ hi₂ h₀.1 h₀.2.1 h₀.2.2.1 h₀.2.2.2

theorem stoppedContactSet_coe_eq_contactSet (A B : ℝ≥0) :
    stoppedContactSet η₁ 0 (A : ℝ≥0∞) η₂ 0 (B : ℝ≥0∞) = contactSet η₁ A η₂ B := by
  ext p
  exact ⟨fun ⟨_, h1, _, h2, h3⟩ => ⟨⟨zero_le, ENNReal.coe_le_coe.mp h1⟩,
      ⟨zero_le, ENNReal.coe_le_coe.mp h2⟩, h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨zero_le, ENNReal.coe_le_coe.mpr h1.2, zero_le,
      ENNReal.coe_le_coe.mpr h2.2, h3⟩⟩

/-- **Aux. lemma 68 (3)**, frozen form (finite lifetimes `A`, `B`): the two stopped curves have a
first contact (`IsFirstContact`) iff their set of minimal contacts is a singleton. -/
theorem exists_isFirstContact_coe_iff {A B : ℝ≥0} (hα : ContinuousOn η₁ (Icc 0 A))
    (hβ : ContinuousOn η₂ (Icc 0 B)) :
    (∃ s₀ t₀ : ℝ≥0, IsFirstContact η₁ A η₂ B s₀ t₀) ↔
      ∃ p, minimalContacts η₁ A η₂ B = {p} := by
  rw [exists_minimalContacts_eq_singleton_iff hα hβ]
  simp only [isFirstContact_iff, stoppedContactSet_coe_eq_contactSet]
  exact ⟨fun ⟨s₀, t₀, h⟩ => ⟨(s₀, t₀), h⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h⟩⟩

/-- **Aux. lemma 68**, frozen form (finite lifetimes): if two injective continuous stopped curves
meet, then either they have a first contact (`IsFirstContact`), or the first projection of their
minimal contacts contains a nondegenerate interval (an oppositely traversed common subarc), or there
are two adjacent minimal contacts (a Jordan lens, part 4). -/
theorem exists_isFirstContact_coe_or_dichotomy {A B : ℝ≥0} (hα : ContinuousOn η₁ (Icc 0 A))
    (hβ : ContinuousOn η₂ (Icc 0 B)) (hαi : InjOn η₁ (Icc 0 A)) (hβi : InjOn η₂ (Icc 0 B))
    (hC : (contactSet η₁ A η₂ B).Nonempty) :
    (∃ s₀ t₀ : ℝ≥0, IsFirstContact η₁ A η₂ B s₀ t₀) ∨
      (∃ a c : ℝ≥0, a < c ∧ Icc a c ⊆ Prod.fst '' minimalContacts η₁ A η₂ B) ∨
      ∃ a b c d : ℝ≥0, (a, b) ∈ minimalContacts η₁ A η₂ B ∧
        (c, d) ∈ minimalContacts η₁ A η₂ B ∧ a < c ∧
          ∀ p ∈ minimalContacts η₁ A η₂ B, p.1 ∉ Ioo a c := by
  by_cases h : ∃ p, minimalContacts η₁ A η₂ B = {p}
  · exact Or.inl ((exists_isFirstContact_coe_iff hα hβ).mpr h)
  · exact Or.inr (minimalContacts_dichotomy hα hβ hαi hβi hC h)

/-- **Common selection from increasing contact order** (Aux. lemma 94, claim 2, p. 317; Theorem W8):
let `η₁|[0, ζ₁]`, `η₂|[0, ζ₂]` be continuous, with `|ηᵢ(t)| → ∞` when `ζᵢ = ∞` (Aux. lemma 67), and
`η₂` injective. If their finite-parameter contacts are encountered in increasing order (as Aux.
lemma 84 gives for ordered proper curves) and some contact exists, then the two first-contact minima
are attained at one common pair: there is a first contact. -/
theorem exists_isFirstContact_of_contact_order (hα : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hβ : ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hαT : ζ₁ = ⊤ → Tendsto (fun s => ‖η₁ s‖) atTop atTop)
    (hβT : ζ₂ = ⊤ → Tendsto (fun t => ‖η₂ t‖) atTop atTop)
    (hβi : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (horder : ∀ p ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂, ∀ q ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂,
      p.1 < q.1 → p.2 < q.2)
    (hne : (stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂).Nonempty) :
    ∃ s₀ t₀ : ℝ≥0, IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ := by
  obtain ⟨p, hp, hpmin⟩ := exists_mem_stoppedContactSet_forall_fst_le hα hβ hβT hne
  obtain ⟨q, hq, hqmin⟩ := exists_mem_stoppedContactSet_forall_snd_le hα hβ hαT hne
  have hpq : p.1 = q.1 := by
    refine le_antisymm (hpmin q hq) (not_lt.mp fun h => ?_)
    exact absurd (hqmin p hp) (not_le.mpr (horder p hp q hq h))
  have hpq2 : p.2 = q.2 := hβi hp.2.2.2.1 hq.2.2.2.1 (by rw [← hp.2.2.2.2, ← hq.2.2.2.2, hpq])
  refine ⟨p.1, p.2, isFirstContact_iff.mpr ⟨hp, fun r hr => ⟨hpmin r hr, ?_⟩⟩⟩
  rw [hpq2]
  exact hqmin r hr

/-- Reduction of the second clause of Theorem 1.5 (iii) ("every interior available contact is the
first contact", Theorem 7.12D) to the absence of later contacts: if `(s₀, t₀)` is the first contact
of injective stopped curves and no contact occurs at a parameter `s > s₀` of the first curve, then
every interior available contact is the first contact. -/
theorem isFirstContact_of_isFirstContact_of_noLater {s₀ t₀ s t : ℝ≥0}
    (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂}) (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (hno : ∀ q ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂, q.1 ≤ s₀)
    (h : IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t) :
    IsFirstContact η₁ ζ₁ η₂ ζ₂ s t := by
  have hle := IsFirstContact.le_of_isInteriorAvailableContact h₀ h
  have hs : s = s₀ :=
    le_antisymm (hno _ (IsInteriorAvailableContact.mem_stoppedContactSet h)) hle.1
  have ht : t = t₀ := hi₂ h.2.1.le h₀.2.1 (by rw [← h.2.2.1, hs, h₀.2.2.1])
  rw [hs, ht]
  exact h₀

/-- **Theorem 1.5 (iii), second clause, pointwise reduction.** For injective stopped curves, if an
interior available contact forces a first contact after which no contact occurs at a later
first-curve parameter (Lemma 7.7 with the critical exclusion 7.12D), then every interior available
contact is the first contact — the conclusion of the second clause of `IsFlowLine.crosses_of_lt` for
one realization. -/
theorem isFirstContact_of_firstContact_noLater (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hfirst : (∃ s t : ℝ≥0, IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀ ∧
        ∀ q ∈ stoppedContactSet η₁ 0 ζ₁ η₂ 0 ζ₂, q.1 ≤ s₀) :
    ∀ s t : ℝ≥0, IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t →
      IsFirstContact η₁ ζ₁ η₂ ζ₂ s t := by
  intro s t h
  obtain ⟨s₀, t₀, h₀, hno⟩ := hfirst ⟨s, t, h⟩
  exact isFirstContact_of_isFirstContact_of_noLater hi₂ h₀ hno h

end Sec7

end InteractingSLE
