/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionFirstContact
import InteractingSLE.Spec.Sec7.InteractionSelection

/-!
# Supplement §10: increasing contact order, common later selection and no return (deterministic)

Packet PROVE-SUPP10 (specification supplement §10, `source/spec/p529-576.md`, pp. 536–541). The finite-parameter
contact relation of two stopped curves `α|[0, T₁]`, `β|[0, T₂]` is `Sec7.stoppedContactSet α 0 T₁ β 0 T₂`
(finite parameters, finite terminal values included, `Tᵢ = ∞` allowed). It is *increasing*
(`ContactsIncreasing`) when `s < s'` forces `t < t'` for any two contacts `(s, t)`, `(s', t')`: "their finite common
points occur in increasing parameter order" (Lemma W6, p. 537).

* **Theorem W8, common selection** (pp. 539–540): "If [the later contact relation] is nonempty, choose one finite
  contact `(u_*, v_*)`. Both coordinate minima are attained in the compact rectangle `[0, u_*] × [V, v_*]`.
  Increasing order makes them a single pair `(u₀, v₀)` and hence a common point `q`." For every start `σ` of the
  second curve, the later contact relation `Sec7.laterContactSet α T₁ β σ T₂` then has a coordinatewise least
  element (`exists_least_laterContactSet_of_contactsIncreasing`). This is exactly the common-attained-selection
  hypothesis of the landed (GR2) identity `Sec7.selected_le_iff` (`selected_le_iff_of_contactsIncreasing`). No
  properness at an infinite lifetime is needed: the rectangle is fixed by one contact.
* **(W8.2)** (p. 540): "Increasing contact order and simplicity give `γᵢ((uᵢ, Lᵢ]) ∩ (γ₁([0, u₀]) ∪ γ₂([0, v₀])) = ∅`"
  (`no_return_of_contactsIncreasing`). Together with the selection, the first path never returns to the second
  prefix before `σ` (`no_return_before_start_of_contactsIncreasing`).
* **Theorem W8, reduction** (pp. 539–540): with the finite global first contact `(a₁, a₂)`: if `σ ≤ a₂` the later
  selection is exactly the first contact (`isLeast_laterContactSet_of_isFirstContact`); if one path terminates at
  the first contact, first-contact no return leaves no later contact for `σ > a₂`
  (`laterContactSet_eq_empty_of_terminated`); if there is no contact at all, there is no later contact
  (`laterContactSet_eq_empty_of_noContact`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp10

open Sec7

variable {X : Type*}

/-- **Increasing contact order** (Lemma W6, p. 537): the finite-parameter contacts of `α|[0, T₁]` and `β|[0, T₂]`
(finite terminal values included) occur in increasing parameter order: `s < s'` forces `t < t'`. -/
def ContactsIncreasing (α : ℝ≥0 → X) (T₁ : ℝ≥0∞) (β : ℝ≥0 → X) (T₂ : ℝ≥0∞) : Prop :=
  ∀ p ∈ stoppedContactSet α 0 T₁ β 0 T₂, ∀ q ∈ stoppedContactSet α 0 T₁ β 0 T₂, p.1 < q.1 → p.2 < q.2

section Increasing

variable {α β : ℝ≥0 → X} {T₁ T₂ : ℝ≥0∞}

/-- For a second curve injective on its available interval, increasing order also holds in the second
parametrization: `t < t'` forces `s < s'`. -/
theorem ContactsIncreasing.fst_lt_of_snd_lt (h : ContactsIncreasing α T₁ β T₂)
    (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂}) {p q : ℝ≥0 × ℝ≥0}
    (hp : p ∈ stoppedContactSet α 0 T₁ β 0 T₂) (hq : q ∈ stoppedContactSet α 0 T₁ β 0 T₂)
    (hlt : p.2 < q.2) : p.1 < q.1 := by
  rcases lt_trichotomy p.1 q.1 with h1 | h1 | h1
  · exact h1
  · have : p.2 = q.2 := hβi hp.2.2.2.1 hq.2.2.2.1 (by rw [← hp.2.2.2.2, ← hq.2.2.2.2, h1])
    exact absurd this hlt.ne
  · exact absurd (h q hq p hp h1) (not_lt.mpr hlt.le)

/-- The later contact relation is a subset of the full contact relation. -/
theorem laterContactSet_subset_stoppedContactSet {σ : ℝ≥0∞} :
    laterContactSet α T₁ β σ T₂ ⊆ stoppedContactSet α 0 T₁ β 0 T₂ :=
  fun _ hp => ⟨zero_le, hp.1, zero_le, hp.2.2.1, hp.2.2.2⟩

variable [TopologicalSpace X] [T2Space X]

/-- **Theorem W8, common selection** (pp. 539–540). Let `α|[0, T₁]`, `β|[0, T₂]` be continuous, `β` injective on
its available interval, and let their contacts be increasing. Then for every start `σ` of the second curve, a
nonempty later contact relation `C_σ` has a coordinatewise least element: both first-contact minima are attained at
one pair, hence at one common point. -/
theorem exists_least_laterContactSet_of_contactsIncreasing (hα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ T₂}) (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hinc : ContactsIncreasing α T₁ β T₂) {σ : ℝ≥0∞}
    (hne : (laterContactSet α T₁ β σ T₂).Nonempty) :
    ∃ p ∈ laterContactSet α T₁ β σ T₂, ∀ q ∈ laterContactSet α T₁ β σ T₂, p.1 ≤ q.1 ∧ p.2 ≤ q.2 := by
  obtain ⟨ps, hps⟩ := hne
  have hIcc₁ : Icc 0 ps.1 ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T₁} := fun s hs =>
    (ENNReal.coe_le_coe.mpr hs.2).trans hps.1
  have hIcc₂ : Icc 0 ps.2 ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T₂} := fun t ht =>
    (ENNReal.coe_le_coe.mpr ht.2).trans hps.2.2.1
  have hK := isCompact_contacts_Icc (hα.mono hIcc₁) (hβ.mono hIcc₂)
  have hσc : IsClosed {q : ℝ≥0 × ℝ≥0 | σ ≤ (q.2 : ℝ≥0∞)} :=
    isClosed_le continuous_const (ENNReal.continuous_coe.comp continuous_snd)
  have hR := hK.inter_right hσc
  obtain ⟨p, hp, hmin⟩ := hR.exists_isMinOn
    ⟨ps, ⟨⟨⟨zero_le, le_rfl⟩, ⟨zero_le, le_rfl⟩⟩, hps.2.2.2⟩, hps.2.1⟩ continuous_fst.continuousOn
  have hpC : p ∈ laterContactSet α T₁ β σ T₂ :=
    ⟨hIcc₁ hp.1.1.1, hp.2, hIcc₂ hp.1.1.2, hp.1.2⟩
  have hsub := laterContactSet_subset_stoppedContactSet (α := α) (β := β) (T₁ := T₁) (T₂ := T₂)
    (σ := σ)
  have hfst : ∀ q ∈ laterContactSet α T₁ β σ T₂, p.1 ≤ q.1 := by
    intro q hq
    by_cases h1 : q.1 ≤ ps.1
    · by_cases h2 : q.2 ≤ ps.2
      · exact hmin ⟨⟨⟨⟨zero_le, h1⟩, ⟨zero_le, h2⟩⟩, hq.2.2.2⟩, hq.2.1⟩
      · have := hinc.fst_lt_of_snd_lt hβi (hsub hps) (hsub hq) (not_le.mp h2)
        exact absurd h1 (not_le.mpr this)
    · exact hp.1.1.1.2.trans (not_le.mp h1).le
  refine ⟨p, hpC, fun q hq => ⟨hfst q hq, ?_⟩⟩
  rcases (hfst q hq).lt_or_eq with h | h
  · exact (hinc p (hsub hpC) q (hsub hq) h).le
  · exact (hβi (hsub hpC).2.2.2.1 (hsub hq).2.2.2.1
      (by rw [← (hsub hpC).2.2.2.2, ← (hsub hq).2.2.2.2, h])).le

/-- **(GR2) under W8's common selection**: increasing contact order supplies the common-attained-selection
hypothesis of the landed lower-rectangle identity `Sec7.selected_le_iff` (Theorem 7.9B, p. 459), for every
start `σ`. -/
theorem selected_le_iff_of_contactsIncreasing (hα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ T₂}) (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hinc : ContactsIncreasing α T₁ β T₂) (σ : ℝ≥0∞) (s t : ℝ≥0) :
    (contactInf₁ (laterContactSet α T₁ β σ T₂) ⊓ T₁ ≤ s ∧
        contactInf₂ (laterContactSet α T₁ β σ T₂) ⊓ T₂ ≤ t) ↔
      (T₁ ≤ s ∧ T₂ ≤ t) ∨
        (σ ≤ t ∧ (α '' {u : ℝ≥0 | u ≤ s ∧ (u : ℝ≥0∞) ≤ T₁} ∩
          β '' {v : ℝ≥0 | σ ≤ v ∧ v ≤ t ∧ (v : ℝ≥0∞) ≤ T₂}).Nonempty) :=
  selected_le_iff (exists_least_laterContactSet_of_contactsIncreasing hα hβ hβi hinc) s t

end Increasing

/-! ### (W8.2): no return after a contact -/

section NoReturn

variable {α β : ℝ≥0 → X} {T₁ T₂ : ℝ≥0∞}

/-- **(W8.2)** (p. 540): "Increasing contact order and simplicity give
`γᵢ((uᵢ, Lᵢ]) ∩ (γ₁([0, u₀]) ∪ γ₂([0, v₀])) = ∅`." For injective curves with increasing contacts, after any contact
`(u₀, v₀)` neither available tail returns to the union of the two prefixes through it. -/
theorem no_return_of_contactsIncreasing (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂}) (hinc : ContactsIncreasing α T₁ β T₂) {u₀ v₀ : ℝ≥0}
    (hp : (u₀, v₀) ∈ stoppedContactSet α 0 T₁ β 0 T₂) :
    (∀ s : ℝ≥0, u₀ < s → (s : ℝ≥0∞) ≤ T₁ → α s ∉ α '' Icc 0 u₀ ∪ β '' Icc 0 v₀) ∧
      ∀ t : ℝ≥0, v₀ < t → (t : ℝ≥0∞) ≤ T₂ → β t ∉ α '' Icc 0 u₀ ∪ β '' Icc 0 v₀ := by
  constructor
  · rintro s hs hsT (⟨u, hu, hus⟩ | ⟨v, hv, hvs⟩)
    · have huT : (u : ℝ≥0∞) ≤ T₁ := (ENNReal.coe_le_coe.mpr hu.2).trans hp.2.1
      exact absurd (hαi huT hsT hus ▸ hu.2) (not_le.mpr hs)
    · have hvT : (v : ℝ≥0∞) ≤ T₂ := (ENNReal.coe_le_coe.mpr hv.2).trans hp.2.2.2.1
      have hq : (s, v) ∈ stoppedContactSet α 0 T₁ β 0 T₂ := ⟨zero_le, hsT, zero_le, hvT, hvs.symm⟩
      exact absurd hv.2 (not_le.mpr (hinc _ hp _ hq hs))
  · rintro t ht htT (⟨u, hu, hut⟩ | ⟨v, hv, hvt⟩)
    · have huT : (u : ℝ≥0∞) ≤ T₁ := (ENNReal.coe_le_coe.mpr hu.2).trans hp.2.1
      have hq : (u, t) ∈ stoppedContactSet α 0 T₁ β 0 T₂ := ⟨zero_le, huT, zero_le, htT, hut⟩
      exact absurd hu.2 (not_le.mpr (hinc.fst_lt_of_snd_lt hβi hp hq ht))
    · have hvT : (v : ℝ≥0∞) ≤ T₂ := (ENNReal.coe_le_coe.mpr hv.2).trans hp.2.2.2.1
      exact absurd (hβi hvT htT hvt ▸ hv.2) (not_le.mpr ht)

/-- **Theorem W8, no return to the second prefix before `σ`** (p. 540: "Together with W7 this proves both original
no-return assertions, including avoidance of the second prefix before `σ`"): at the least later contact
`(u₀, v₀)`, the first tail avoids the whole second prefix `β([0, v₀])`, in particular `β([0, σ))`. -/
theorem no_return_before_start_of_contactsIncreasing (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂}) (hinc : ContactsIncreasing α T₁ β T₂) {σ : ℝ≥0∞}
    {u₀ v₀ : ℝ≥0} (hp : (u₀, v₀) ∈ laterContactSet α T₁ β σ T₂) :
    ∀ s : ℝ≥0, u₀ < s → (s : ℝ≥0∞) ≤ T₁ → α s ∉ β '' {v | (v : ℝ≥0∞) < σ} := by
  rintro s hs hsT ⟨v, hv, hvs⟩
  have hvv₀ : v ≤ v₀ := by
    have : (v : ℝ≥0∞) ≤ v₀ := hv.le.trans hp.2.1
    exact ENNReal.coe_le_coe.mp this
  exact (no_return_of_contactsIncreasing hαi hβi hinc
    (laterContactSet_subset_stoppedContactSet hp)).1 s hs hsT (Or.inr ⟨v, ⟨zero_le, hvv₀⟩, hvs⟩)

end NoReturn

/-! ### Theorem W8: reduction to the first contact -/

section Reduction

variable {α β : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0∞}

/-- **Theorem W8** (p. 539): "If the available full original paths have no finite global contact, there is no
finite later contact." -/
theorem laterContactSet_eq_empty_of_noContact
    (h : ∀ s t : ℝ≥0, (s : ℝ≥0∞) ≤ T₁ → (t : ℝ≥0∞) ≤ T₂ → α s ≠ β t) (σ : ℝ≥0∞) :
    laterContactSet α T₁ β σ T₂ = ∅ :=
  eq_empty_of_forall_notMem fun p hp => h p.1 p.2 hp.1 hp.2.2.1 hp.2.2.2

/-- **Theorem W8** (p. 540): "If `σ ≤ a₂`, the later selection is exactly this first contact, so its conclusions
already apply." -/
theorem isLeast_laterContactSet_of_isFirstContact {a₁ a₂ : ℝ≥0}
    (h₀ : IsFirstContact α T₁ β T₂ a₁ a₂) {σ : ℝ≥0∞} (hσ : σ ≤ a₂) :
    (a₁, a₂) ∈ laterContactSet α T₁ β σ T₂ ∧
      ∀ q ∈ laterContactSet α T₁ β σ T₂, a₁ ≤ q.1 ∧ a₂ ≤ q.2 :=
  ⟨⟨h₀.1, hσ, h₀.2.1, h₀.2.2.1⟩, fun q hq => h₀.2.2.2 q.1 q.2 hq.1 hq.2.2.1 hq.2.2.2⟩

/-- **Theorem W8** (p. 540): "If one path terminates at that first contact, first-contact no return makes every
second suffix starting strictly after `a₂` disjoint from the other available prefix. There is then no new finite
later contact." -/
theorem laterContactSet_eq_empty_of_terminated (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂}) {a₁ a₂ : ℝ≥0} (h₀ : IsFirstContact α T₁ β T₂ a₁ a₂)
    (hterm : (a₁ : ℝ≥0∞) = T₁ ∨ (a₂ : ℝ≥0∞) = T₂) {σ : ℝ≥0∞} (hσ : (a₂ : ℝ≥0∞) < σ) :
    laterContactSet α T₁ β σ T₂ = ∅ := by
  refine eq_empty_of_forall_notMem fun p hp => ?_
  have ha₂p : a₂ < p.2 := ENNReal.coe_lt_coe.mp (hσ.trans_le hp.2.1)
  rcases hterm with h | h
  · have hp1 : p.1 ≤ a₁ := ENNReal.coe_le_coe.mp (h ▸ hp.1)
    exact (no_return_of_firstContact hαi hβi h₀.1 h₀.2.1 h₀.2.2.1 h₀.2.2.2).2 p.2 ha₂p hp.2.2.1
      (Or.inl ⟨p.1, ⟨zero_le, hp1⟩, hp.2.2.2⟩)
  · exact absurd (h ▸ hp.2.2.1) (not_le.mpr (ENNReal.coe_lt_coe.mpr ha₂p))

end Reduction

end Supp10

end InteractingSLE
