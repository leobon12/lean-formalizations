/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionContacts
import InteractingSLE.Spec.Supplement.S9Completion

/-!
# Supplement §9: the contact combinatorics of Lemma W1 and of the cuts in Theorem W5

Packet PROVE-SUPP9 (specification supplement §9, `source/spec/p529-576.md`, pp. 529–535). The deterministic
order-theoretic content of Lemma W1 (incoming rational cuts for a backwards contact, pp. 529–530) and of the
"incoming active rational cuts" of Theorem W5's proof (pp. 534–535), for continuous injective curves in any
Hausdorff space, with the contact relation `Sec7.contactSet` of Aux. lemma 68.

* `EarlierContactsIncreasing α A β t`: contacts with second parameter `< t` are increasing ("All contacts with
  second parameter strictly below `t` have increasing coordinates, by the proper-completion boundary-order
  theorem", p. 530). The boundary-order theorem itself (G5, Aux. lemma 84) is not in Lean; its exact statement
  is `OrderedContactOrderStatement`, and `earlierContactsIncreasing_of_contactOrder` is the bridge.
* **Lemma W1, order part** (`exists_upperContact`, `lowerContact_or`, `exists_matchedGap`, `w1_cuts`): given
  `p = α(a) = β(t)` and an earlier contact `q₀ = α(b₀) = β(v₀)` with `a < b₀`, `v₀ < t`, there are cuts `r ∈ R`,
  `s ∈ S` (any dense sets of parameters, e.g. rational interior trace times) and an earlier contact
  `q = α(b) = β(v)` with `r < a < b`, `s < v < t`, such that the only contacts of `α([r, b])` and `β([s, t])` are
  `p` and `q`, (W1.1) `α([r, a]) ∩ β([s, v]) = ∅`, the fresh portions avoid both old prefixes, and the tips are
  distinct (items 2–3 of W1). `w1_cuts_of_ordered` adds item 1's first clause: the old pair has ordered proper
  completions. The rest of item 1 (activity of the tips in the joint unbounded component, Aux. lemma 90) and the
  prime-end order `w_β < w_α` (Aux. lemma 85) are conformal statements and are not proved here.
* **W5, cut selection** (`exists_incomingCuts`, p. 534–535): at `p = α(a) = β(τ)`, the last contact of the
  current rectangle, the absence of a common open subarc (`HasCommonOpenSubarc`, W0b) gives cuts `r ∈ R`, `s ∈ S`
  arbitrarily close to `(a, τ)` whose fresh incoming arcs avoid both old prefixes ("The closed increasing relation
  has matched open gaps arbitrarily close to `p`; otherwise one of the curves would contain a common open
  subarc").

The mathematical source does not need W1's hypothesis "no common open subarc before `t`" for items 2–3: the
backwards contact `p` is automatically separated from the earlier contacts (first paragraph of W1's proof). Only
W1's own hypotheses that are used appear here; `0 < a` and "`α` does not visit `β`'s seed after time `0`" (W0a, or
injectivity for a common seed) are needed when no earlier contact precedes `a`.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Filter
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp9

open Sec7

variable {X : Type*}

/-- `α([0, a])` and `β([0, c])` contain a common nontrivial open subarc: an open subarc `α((x₁, x₂))` of the first
prefix lies in the second one (Lemma W0b, p. 529; for injective curves this is the symmetric notion). -/
def HasCommonOpenSubarc (α : ℝ≥0 → X) (a : ℝ≥0) (β : ℝ≥0 → X) (c : ℝ≥0) : Prop :=
  ∃ x₁ x₂ : ℝ≥0, x₁ < x₂ ∧ x₂ ≤ a ∧ α '' Ioo x₁ x₂ ⊆ β '' Icc 0 c

/-- The contacts of `α|[0, A]` and `β|[0, t]` with second parameter strictly below `t` are increasing
(Lemma W1's proof, p. 530). -/
def EarlierContactsIncreasing (α : ℝ≥0 → X) (A : ℝ≥0) (β : ℝ≥0 → X) (t : ℝ≥0) : Prop :=
  ∀ p ∈ contactSet α A β t, ∀ q ∈ contactSet α A β t, p.2 < t → q.2 < t → p.1 < q.1 → p.2 < q.2

theorem disjoint_image_image_iff {f g : ℝ≥0 → X} {s t : Set ℝ≥0} :
    Disjoint (f '' s) (g '' t) ↔ ∀ x ∈ s, ∀ y ∈ t, f x ≠ g y := by
  constructor
  · intro h x hx y hy hxy
    exact Set.disjoint_left.1 h ⟨x, hx, rfl⟩ ⟨y, hy, hxy.symm⟩
  · intro h
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact h x hx y hy hxy.symm

section W1

variable {α β : ℝ≥0 → X} {A t : ℝ≥0}

/-- At the backwards contact `p = α(a) = β(t)`, the only contact with second parameter `t` is `p`. -/
theorem fst_eq_of_snd_eq (hαi : InjOn α (Icc 0 A)) {a : ℝ≥0} (ha : a ≤ A) (hp : α a = β t)
    {q : ℝ≥0 × ℝ≥0} (hq : q ∈ contactSet α A β t) (h : q.2 = t) : q.1 = a :=
  hαi hq.1 ⟨zero_le, ha⟩ (by rw [hq.2.2, h, hp])

/-- At the backwards contact `p = α(a) = β(t)`, the only contact with first parameter `a` is `p`. -/
theorem snd_eq_of_fst_eq (hβi : InjOn β (Icc 0 t)) {a : ℝ≥0} (hp : α a = β t)
    {q : ℝ≥0 × ℝ≥0} (hq : q ∈ contactSet α A β t) (h : q.1 = a) : q.2 = t :=
  hβi hq.2.1 ⟨zero_le, le_rfl⟩ (by rw [← hq.2.2, h, hp])

variable [TopologicalSpace X] [T2Space X]

/-- **Lemma W1's proof, the upper contact** (p. 530): "let `(b, v)` be the first earlier contact with first
parameter above `a`. The latter exists since `(b₀, v₀)` does. These extrema are attained." Every contact with first
parameter in `(a, b₀]` has second parameter at most `v₀`, so a minimizing sequence cannot approach `p`. -/
theorem exists_upperContact (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 t))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 t)) (hinc : EarlierContactsIncreasing α A β t)
    {a b₀ v₀ : ℝ≥0} (ha : a ≤ A) (hp : α a = β t) (hab : a < b₀) (hb₀ : b₀ ≤ A) (hv₀ : v₀ < t)
    (hq₀ : α b₀ = β v₀) :
    ∃ b v : ℝ≥0, (b, v) ∈ contactSet α A β t ∧ a < b ∧ v < t ∧
      ∀ q ∈ contactSet α A β t, a < q.1 → b ≤ q.1 := by
  have hq₀C : ((b₀, v₀) : ℝ≥0 × ℝ≥0) ∈ contactSet α A β t := ⟨⟨zero_le, hb₀⟩, ⟨zero_le, hv₀.le⟩, hq₀⟩
  have hlow : ∀ q ∈ contactSet α A β t, a < q.1 → q.1 ≤ b₀ → q.2 ≤ v₀ := by
    intro q hq h1 h2
    have hqt : q.2 < t := lt_of_le_of_ne hq.2.1.2 fun h => (ne_of_gt h1) (fst_eq_of_snd_eq hαi ha hp hq h)
    rcases h2.lt_or_eq with h2 | h2
    · exact (hinc q hq _ hq₀C hqt hv₀ h2).le
    · exact (congrArg Prod.snd (eq_of_mem_contactSet_of_fst_eq hβi hq hq₀C h2)).le
  set K := contactSet α A β t ∩
    (({q : ℝ≥0 × ℝ≥0 | a ≤ q.1} ∩ {q | q.1 ≤ b₀}) ∩ {q | q.2 ≤ v₀}) with hK_def
  have hK : IsCompact K := (isCompact_contactSet hα hβ).inter_right
    (((isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_fst continuous_const)).inter
      (isClosed_le continuous_snd continuous_const))
  obtain ⟨⟨b, v⟩, hbK, hmin⟩ :=
    hK.exists_isMinOn ⟨(b₀, v₀), hq₀C, ⟨hab.le, (le_rfl : b₀ ≤ b₀)⟩, (le_rfl : v₀ ≤ v₀)⟩
      continuous_fst.continuousOn
  have hb1 : a ≤ b := hbK.2.1.1
  have hb2 : b ≤ b₀ := hbK.2.1.2
  have hvv : v ≤ v₀ := hbK.2.2
  have hab' : a < b := by
    rcases hb1.lt_or_eq with h | h
    · exact h
    · exact absurd (snd_eq_of_fst_eq hβi hp hbK.1 h.symm) (ne_of_lt (hvv.trans_lt hv₀))
  refine ⟨b, v, hbK.1, hab', hvv.trans_lt hv₀, fun q hq hq1 => ?_⟩
  rcases le_or_gt q.1 b₀ with h | h
  · exact hmin ⟨hq, ⟨hq1.le, h⟩, hlow q hq hq1 h⟩
  · exact hb2.trans h.le

/-- **Lemma W1's proof, the lower contact** (p. 530): "Let `(a₋, v₋)` be the last earlier contact with first
parameter below `a`, if one exists. […] For the lower one all relevant second parameters are at most `v₀ < t`, so
compactness applies." -/
theorem lowerContact_or (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 t))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 t)) (hinc : EarlierContactsIncreasing α A β t)
    {a b₀ v₀ : ℝ≥0} (ha : a ≤ A) (hp : α a = β t) (hab : a < b₀) (hb₀ : b₀ ≤ A) (hv₀ : v₀ < t)
    (hq₀ : α b₀ = β v₀) :
    (∀ q ∈ contactSet α A β t, a ≤ q.1) ∨
      ∃ a' v' : ℝ≥0, (a', v') ∈ contactSet α A β t ∧ a' < a ∧ v' < v₀ ∧
        ∀ q ∈ contactSet α A β t, q.1 < a → q.1 ≤ a' := by
  have hq₀C : ((b₀, v₀) : ℝ≥0 × ℝ≥0) ∈ contactSet α A β t := ⟨⟨zero_le, hb₀⟩, ⟨zero_le, hv₀.le⟩, hq₀⟩
  have hbelow : ∀ q ∈ contactSet α A β t, q.1 < a → q.2 < v₀ := by
    intro q hq h1
    have hqt : q.2 < t := lt_of_le_of_ne hq.2.1.2 fun h => (ne_of_lt h1) (fst_eq_of_snd_eq hαi ha hp hq h)
    exact hinc q hq _ hq₀C hqt hv₀ (h1.trans hab)
  set K := contactSet α A β t ∩ ({q : ℝ≥0 × ℝ≥0 | q.1 ≤ a} ∩ {q | q.2 ≤ v₀}) with hK_def
  have hK : IsCompact K := (isCompact_contactSet hα hβ).inter_right
    ((isClosed_le continuous_fst continuous_const).inter (isClosed_le continuous_snd continuous_const))
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine Or.inl fun q hq => not_lt.1 fun h => ?_
    have : q ∈ K := ⟨hq, h.le, (hbelow q hq h).le⟩
    rw [hKe] at this
    exact this
  · obtain ⟨⟨a', v'⟩, haK, hmax⟩ := hK.exists_isMaxOn hKne continuous_fst.continuousOn
    have ha1 : a' ≤ a := haK.2.1
    have hvv : v' ≤ v₀ := haK.2.2
    have ha' : a' < a := by
      rcases ha1.lt_or_eq with h | h
      · exact h
      · exact absurd (snd_eq_of_fst_eq hβi hp haK.1 h) (ne_of_lt (hvv.trans_lt hv₀))
    refine Or.inr ⟨a', v', haK.1, ha', hbelow _ haK.1 ha', fun q hq h => ?_⟩
    exact hmax ⟨hq, h.le, (hbelow q hq h).le⟩

/-- **Lemma W1's proof, the matched contact-free gap** (p. 530): "Increasing order now gives a matched
contact-free gap `(a₋, b)` and `(v₋, v)`, with `a` strictly inside the first interval. If the lower contact is
absent, use the initial seeds as the lower ends of these intervals." The gap is recorded by its lower ends
`lo₁ < a`, `lo₂ < v`: every earlier contact with first parameter below `b` has first parameter at most `lo₁`, and
then second parameter at most `lo₂`. -/
theorem exists_matchedGap (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 t))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 t)) (hinc : EarlierContactsIncreasing α A β t)
    {a b₀ v₀ : ℝ≥0} (ha0 : 0 < a) (ha : a ≤ A) (hp : α a = β t) (hab : a < b₀) (hb₀ : b₀ ≤ A)
    (hv₀ : v₀ < t) (hq₀ : α b₀ = β v₀) (hβ0 : ∀ x ∈ Icc 0 A, α x = β 0 → x = 0) :
    ∃ b v lo₁ lo₂ : ℝ≥0, (b, v) ∈ contactSet α A β t ∧ a < b ∧ v < t ∧ lo₁ < a ∧ lo₂ < v ∧
      (∀ q ∈ contactSet α A β t, q.2 < t → q.1 < b → q.1 ≤ lo₁) ∧
      (∀ q ∈ contactSet α A β t, q.1 ≤ lo₁ → q.2 ≤ lo₂) := by
  obtain ⟨b, v, hbv, hab', hvt, hbmin⟩ := exists_upperContact hα hβ hαi hβi hinc ha hp hab hb₀ hv₀ hq₀
  -- an earlier contact below `b` has first parameter below `a`
  have hbelow_b : ∀ q ∈ contactSet α A β t, q.2 < t → q.1 < b → q.1 < a := by
    intro q hq hqt hqb
    rcases lt_trichotomy q.1 a with h | h | h
    · exact h
    · exact absurd (snd_eq_of_fst_eq hβi hp hq h) (ne_of_lt hqt)
    · exact absurd (hbmin q hq h) (not_le.2 hqb)
  rcases lowerContact_or hα hβ hαi hβi hinc ha hp hab hb₀ hv₀ hq₀ with hnone | ⟨a', v', hav, ha', hv', hamax⟩
  · -- no earlier contact below `a`: the seeds are the lower ends
    have hv0 : 0 < v := by
      refine pos_iff_ne_zero.2 fun hv => ?_
      have hb0 : b = 0 := hβ0 b hbv.1 (by rw [hbv.2.2, hv])
      exact absurd hab' (by rw [hb0]; exact not_lt.2 zero_le)
    refine ⟨b, v, 0, 0, hbv, hab', hvt, ha0, hv0, fun q hq hqt hqb => ?_, fun q hq hq0 => ?_⟩
    · exact absurd (hnone q hq) (not_le.2 (hbelow_b q hq hqt hqb))
    · exact absurd (hnone q hq) (not_le.2 (lt_of_le_of_lt hq0 ha0))
  · have hv't : v' < t := hv'.trans hv₀
    refine ⟨b, v, a', v', hbv, hab', hvt, ha', hinc _ hav _ hbv hv't hvt (ha'.trans hab'),
      fun q hq hqt hqb => hamax q hq (hbelow_b q hq hqt hqb), fun q hq hqa => ?_⟩
    have hqt : q.2 < t := lt_of_le_of_ne hq.2.1.2 fun h =>
      (ne_of_lt (lt_of_le_of_lt hqa ha')) (fst_eq_of_snd_eq hαi ha hp hq h)
    rcases hqa.lt_or_eq with h | h
    · exact (hinc q hq _ hav hqt hv't h).le
    · exact (congrArg Prod.snd (eq_of_mem_contactSet_of_fst_eq hβi hq hav h)).le

/-- **Lemma W1, items 2–3** (pp. 529–530): rational cuts `r ∈ R`, `s ∈ S` (`R`, `S` dense, e.g. the rational
interior trace times) and an earlier contact `q = α(b) = β(v)` with `r < a < b`, `s < v < t`, such that

* the only contacts of `α([r, b])` and `β([s, t])` are `p = α(a) = β(t)` and `q`;
* (W1.1) `α([r, a]) ∩ β([s, v]) = ∅`;
* the fresh portions `α((r, b])`, `β((s, t])` avoid both old prefixes `α([0, r])`, `β([0, s])`;
* the current tips are distinct: `α(r) ≠ β(s)`.

"The same conclusion holds with the paths and left/right orientations exchanged": apply this lemma to `β`, `α`
(it is stated for arbitrary curves). -/
theorem w1_cuts (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 t))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 t)) (hinc : EarlierContactsIncreasing α A β t)
    {a b₀ v₀ : ℝ≥0} (ha0 : 0 < a) (ha : a ≤ A) (hp : α a = β t) (hab : a < b₀) (hb₀ : b₀ ≤ A)
    (hv₀ : v₀ < t) (hq₀ : α b₀ = β v₀) (hβ0 : ∀ x ∈ Icc 0 A, α x = β 0 → x = 0)
    {R S : Set ℝ≥0} (hR : Dense R) (hS : Dense S) :
    ∃ r s b v : ℝ≥0, r ∈ R ∧ s ∈ S ∧ r < a ∧ a < b ∧ b ≤ A ∧ s < v ∧ v < t ∧ α b = β v ∧
      α r ≠ β s ∧
      (∀ x ∈ Icc r b, ∀ y ∈ Icc s t, α x = β y → (x = a ∧ y = t) ∨ (x = b ∧ y = v)) ∧
      Disjoint (α '' Icc r a) (β '' Icc s v) ∧
      Disjoint (α '' Ioc r b) (β '' Icc 0 s) ∧ Disjoint (β '' Ioc s t) (α '' Icc 0 r) ∧
      Disjoint (α '' Ioc r b) (α '' Icc 0 r) ∧ Disjoint (β '' Ioc s t) (β '' Icc 0 s) := by
  obtain ⟨b, v, lo₁, lo₂, hbv, hab', hvt, hlo₁, hlo₂, hP1, hP2⟩ :=
    exists_matchedGap hα hβ hαi hβi hinc ha0 ha hp hab hb₀ hv₀ hq₀ hβ0
  obtain ⟨r, hrR, hr1, hr2⟩ := hR.exists_between hlo₁
  obtain ⟨s, hsS, hs1, hs2⟩ := hS.exists_between hlo₂
  have hbA : b ≤ A := hbv.1.2
  have hmem : ∀ x y : ℝ≥0, x ≤ A → y ≤ t → α x = β y → ((x, y) : ℝ≥0 × ℝ≥0) ∈ contactSet α A β t :=
    fun x y hx hy hxy => ⟨⟨zero_le, hx⟩, ⟨zero_le, hy⟩, hxy⟩
  -- the two contacts in the fresh box
  have hbox : ∀ x ∈ Icc r b, ∀ y ∈ Icc s t, α x = β y → (x = a ∧ y = t) ∨ (x = b ∧ y = v) := by
    intro x hx y hy hxy
    have hq := hmem x y (hx.2.trans hbA) hy.2 hxy
    rcases hy.2.lt_or_eq with hyt | hyt
    · rcases hx.2.lt_or_eq with hxb | hxb
      · exact absurd (hP1 _ hq hyt hxb) (not_le.2 (hr1.trans_le hx.1))
      · exact Or.inr ⟨hxb, congrArg Prod.snd (eq_of_mem_contactSet_of_fst_eq hβi hq hbv hxb)⟩
    · exact Or.inl ⟨fst_eq_of_snd_eq hαi ha hp hq hyt, hyt⟩
  refine ⟨r, s, b, v, hrR, hsS, hr2, hab', hbA, hs2, hvt, hbv.2.2, ?_, hbox, ?_, ?_, ?_, ?_, ?_⟩
  · -- distinct tips
    intro hrs
    rcases hbox r ⟨le_rfl, (hr2.trans hab').le⟩ s ⟨le_rfl, (hs2.trans hvt).le⟩ hrs with h | h
    · exact (ne_of_lt hr2) h.1
    · exact (ne_of_lt (hr2.trans hab')) h.1
  · -- (W1.1)
    refine disjoint_image_image_iff.2 fun x hx y hy hxy => ?_
    rcases hbox x ⟨hx.1, hx.2.trans hab'.le⟩ y ⟨hy.1, hy.2.trans hvt.le⟩ hxy with h | h
    · exact absurd (h.2 ▸ hy.2) (not_le.2 hvt)
    · exact absurd (h.1 ▸ hx.2) (not_le.2 hab')
  · -- the first fresh portion avoids the old second prefix
    refine disjoint_image_image_iff.2 fun x hx y hy hxy => ?_
    have hyt : y < t := hy.2.trans_lt (hs2.trans hvt)
    have hq := hmem x y (hx.2.trans hbA) hyt.le hxy
    rcases hx.2.lt_or_eq with hxb | hxb
    · exact absurd (hP1 _ hq hyt hxb) (not_le.2 (hr1.trans hx.1))
    · have : y = v := congrArg Prod.snd (eq_of_mem_contactSet_of_fst_eq hβi hq hbv hxb)
      exact absurd (this ▸ hy.2) (not_le.2 hs2)
  · -- the second fresh portion avoids the old first prefix
    refine disjoint_image_image_iff.2 fun y hy x hx hxy => ?_
    have hxA : x ≤ A := hx.2.trans (hr2.trans_le ha).le
    have hq := hmem x y hxA hy.2 hxy.symm
    rcases hy.2.lt_or_eq with hyt | hyt
    · have h1 := hP1 _ hq hyt (hx.2.trans_lt (hr2.trans hab'))
      exact absurd (hP2 _ hq h1) (not_le.2 (hs1.trans hy.1))
    · exact absurd (fst_eq_of_snd_eq hαi ha hp hq hyt ▸ hx.2) (not_le.2 hr2)
  · -- own injectivity of the first path
    refine disjoint_image_image_iff.2 fun x hx x' hx' hxx => ?_
    have := hαi ⟨zero_le, hx.2.trans hbA⟩ ⟨zero_le, hx'.2.trans (hr2.trans_le ha).le⟩ hxx
    exact absurd (this ▸ hx'.2) (not_le.2 hx.1)
  · -- own injectivity of the second path
    refine disjoint_image_image_iff.2 fun y hy y' hy' hyy => ?_
    have := hβi ⟨zero_le, hy.2⟩ ⟨zero_le, hy'.2.trans (hs2.trans hvt).le⟩ hyy
    exact absurd (this ▸ hy'.2) (not_le.2 hy.1)


/-- **Theorem W5's proof, the incoming cuts** (pp. 534–535): at `p = α(a) = β(τ)`, the largest contact of the
current rectangle, with increasing earlier contacts and no common open subarc before `τ` (W0b), there are cuts
`r ∈ R`, `s ∈ S` within `δ` of `(a, τ)` whose fresh incoming arcs `α((r, a])`, `β((s, τ])` avoid both old prefixes
`β([0, s])`, `α([0, r])`, with distinct tips. "If contacts accumulate at `p` […] The closed increasing relation has
matched open gaps arbitrarily close to `p`; otherwise one of the curves would contain a common open subarc. Choose
rational interior parameters in one such gap. If earlier contacts do not accumulate at `p`, choose rational cuts in
the two final contact-free incoming arcs instead." Closeness in the second parameter uses that contacts with first
parameter near `a` have second parameter near `τ` (compactness of the contact set). -/
theorem exists_incomingCuts {a τ : ℝ≥0} (hα : ContinuousOn α (Icc 0 a)) (hβ : ContinuousOn β (Icc 0 τ))
    (hαi : InjOn α (Icc 0 a)) (hβi : InjOn β (Icc 0 τ)) (hinc : EarlierContactsIncreasing α a β τ)
    (hp : α a = β τ) (ha0 : 0 < a) (hτ0 : 0 < τ) (harc : ∀ v < τ, ¬ HasCommonOpenSubarc α a β v)
    {R S : Set ℝ≥0} (hR : Dense R) (hS : Dense S) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ r s : ℝ≥0, r ∈ R ∧ s ∈ S ∧ a - δ < r ∧ r < a ∧ τ - δ < s ∧ s < τ ∧ α r ≠ β s ∧
      Disjoint (α '' Ioc r a) (β '' Icc 0 s) ∧ Disjoint (β '' Ioc s τ) (α '' Icc 0 r) := by
  set C := contactSet α a β τ with hC_def
  have hCc : IsCompact C := isCompact_contactSet hα hβ
  have hpC : ((a, τ) : ℝ≥0 × ℝ≥0) ∈ C := ⟨⟨zero_le, le_rfl⟩, ⟨zero_le, le_rfl⟩, hp⟩
  have hearly : ∀ q ∈ C, q.1 < a → q.2 < τ := fun q hq h =>
    lt_of_le_of_ne hq.2.1.2 fun h' => (ne_of_lt h) (fst_eq_of_snd_eq hαi le_rfl hp hq h')
  have hmono : ∀ q ∈ C, ∀ q' ∈ C, q.1 < q'.1 → q.2 < q'.2 := by
    intro q hq q' hq' h
    have hqa : q.1 < a := h.trans_le hq'.1.2
    rcases hq'.2.1.2.lt_or_eq with h' | h'
    · exact hinc q hq q' hq' (hearly q hq hqa) h' h
    · exact h' ▸ hearly q hq hqa
  have hle : ∀ q ∈ C, ∀ q' ∈ C, q.1 ≤ q'.1 → q.2 ≤ q'.2 := by
    intro q hq q' hq' h
    rcases h.lt_or_eq with h | h
    · exact (hmono q hq q' hq' h).le
    · exact (congrArg Prod.snd (eq_of_mem_contactSet_of_fst_eq hβi hq hq' h)).le
  -- Step A: contacts with first parameter beyond `m` have second parameter beyond `τ - δ`
  have hτδ : τ - δ < τ := tsub_lt_self hτ0 hδ
  obtain ⟨m, hma, hm⟩ : ∃ m < a, ∀ q ∈ C, m < q.1 → τ - δ < q.2 := by
    set K := C ∩ {q : ℝ≥0 × ℝ≥0 | q.2 ≤ τ - δ}
    have hK : IsCompact K := hCc.inter_right (isClosed_le continuous_snd continuous_const)
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨0, ha0, fun q hq _ => not_le.1 fun h => ?_⟩
      have : q ∈ K := ⟨hq, h⟩
      rw [hKe] at this
      exact this
    · obtain ⟨q₀, hq₀K, hmax⟩ := hK.exists_isMaxOn hKne continuous_fst.continuousOn
      have hq₀2 : q₀.2 ≤ τ - δ := hq₀K.2
      refine ⟨q₀.1, lt_of_le_of_ne hq₀K.1.1.2 fun h => ?_, fun q hq h => not_le.1 fun h' => ?_⟩
      · exact absurd (snd_eq_of_fst_eq hβi hp hq₀K.1 h) (ne_of_lt (hq₀2.trans_lt hτδ))
      · exact absurd (hmax ⟨hq, h'⟩) (not_le.2 h)
  set m' := max m (a - δ) with hm'_def
  have hm'a : m' < a := max_lt hma (tsub_lt_self ha0 hδ)
  by_cases hgap : ∃ x ∈ Ioo m' a, ∀ q ∈ C, q.1 ≠ x
  · obtain ⟨x, hx, hxC⟩ := hgap
    -- the first contact after `x`
    set K₂ := C ∩ {q : ℝ≥0 × ℝ≥0 | x ≤ q.1}
    have hK₂ : IsCompact K₂ := hCc.inter_right (isClosed_le continuous_const continuous_fst)
    obtain ⟨⟨h₁, h₂⟩, hhK, hhmin⟩ :=
      hK₂.exists_isMinOn ⟨(a, τ), hpC, hx.2.le⟩ continuous_fst.continuousOn
    have hxh : x < h₁ := lt_of_le_of_ne hhK.2 fun h => hxC _ hhK.1 h.symm
    have hhi : ∀ q ∈ C, x ≤ q.1 → h₁ ≤ q.1 := fun q hq h => hhmin ⟨hq, h⟩
    have hh₂ : τ - δ < h₂ := hm _ hhK.1 ((le_max_left _ _).trans_lt (hx.1.trans hxh))
    have hge : ∀ q ∈ C, x < q.1 → h₂ ≤ q.2 := fun q hq h => hle _ hhK.1 q hq (hhi q hq h.le)
    -- the lower ends of the gap
    obtain ⟨lo₁, lo₂, hlo₁, hlo₁h, hlo₂, hlo₂h, hlow⟩ : ∃ lo₁ lo₂ : ℝ≥0, m' ≤ lo₁ ∧ lo₁ < h₁ ∧
        τ - δ ≤ lo₂ ∧ lo₂ < h₂ ∧ ∀ q ∈ C, q.1 ≤ x → q.1 ≤ lo₁ ∧ q.2 ≤ lo₂ := by
      set K₁ := C ∩ {q : ℝ≥0 × ℝ≥0 | q.1 ≤ x}
      have hK₁ : IsCompact K₁ := hCc.inter_right (isClosed_le continuous_fst continuous_const)
      rcases K₁.eq_empty_or_nonempty with hKe | hKne
      · refine ⟨m', τ - δ, le_rfl, hx.1.trans hxh, le_rfl, hh₂, fun q hq h => ?_⟩
        have : q ∈ K₁ := ⟨hq, h⟩
        rw [hKe] at this
        exact this.elim
      · obtain ⟨⟨l₁, l₂⟩, hlK, hlmax⟩ := hK₁.exists_isMaxOn hKne continuous_fst.continuousOn
        have hl₁x : l₁ < x := lt_of_le_of_ne hlK.2 (hxC _ hlK.1)
        have hl₂ : l₂ < h₂ := hmono _ hlK.1 _ hhK.1 (hl₁x.trans hxh)
        refine ⟨max l₁ m', max l₂ (τ - δ), le_max_right _ _, max_lt (hl₁x.trans hxh) (hx.1.trans hxh),
          le_max_right _ _, max_lt hl₂ hh₂, fun q hq h => ?_⟩
        have hq1 : q.1 ≤ l₁ := hlmax ⟨hq, h⟩
        exact ⟨hq1.trans (le_max_left _ _), (hle q hq _ hlK.1 hq1).trans (le_max_left _ _)⟩
    obtain ⟨r, hrR, hr1, hr2⟩ := hR.exists_between hlo₁h
    obtain ⟨s, hsS, hs1, hs2⟩ := hS.exists_between hlo₂h
    have hh₁a : h₁ ≤ a := hhK.1.1.2
    have hh₂τ : h₂ ≤ τ := hhK.1.2.1.2
    have hra : r < a := hr2.trans_le hh₁a
    have hsτ : s < τ := hs2.trans_le hh₂τ
    have hmem : ∀ x' y : ℝ≥0, x' ≤ a → y ≤ τ → α x' = β y → ((x', y) : ℝ≥0 × ℝ≥0) ∈ C :=
      fun x' y hx' hy hxy => ⟨⟨zero_le, hx'⟩, ⟨zero_le, hy⟩, hxy⟩
    refine ⟨r, s, hrR, hsS, ((le_max_right _ _).trans hlo₁).trans_lt hr1, hra, hlo₂.trans_lt hs1, hsτ,
      ?_, ?_, ?_⟩
    · intro hrs
      have hq := hmem r s hra.le hsτ.le hrs
      rcases le_or_gt r x with h | h
      · exact absurd (hlow _ hq h).1 (not_le.2 hr1)
      · exact absurd (hhi _ hq h.le) (not_le.2 hr2)
    · refine disjoint_image_image_iff.2 fun x' hx' y hy hxy => ?_
      have hq := hmem x' y hx'.2 (hy.2.trans hsτ.le) hxy
      rcases le_or_gt x' x with h | h
      · exact absurd ((hlow _ hq h).1.trans_lt hr1) (not_lt.2 hx'.1.le)
      · exact absurd ((hge _ hq h).trans hy.2) (not_le.2 hs2)
    · refine disjoint_image_image_iff.2 fun y hy x' hx' hxy => ?_
      have hq := hmem x' y (hx'.2.trans hra.le) hy.2 hxy.symm
      rcases le_or_gt x x' with h | h
      · exact absurd ((hhi _ hq h).trans hx'.2) (not_le.2 hr2)
      · exact absurd ((hlow _ hq h.le).2.trans_lt hs1) (not_lt.2 hy.1.le)
  · -- no gap near `a`: a common open subarc
    push Not at hgap
    obtain ⟨x₂, hx₂⟩ := exists_between hm'a
    obtain ⟨q₂, hq₂C, hq₂⟩ := hgap x₂ hx₂
    have hq₂τ : q₂.2 < τ := hearly q₂ hq₂C (hq₂ ▸ hx₂.2)
    refine absurd ⟨m', x₂, hx₂.1, hx₂.2.le, ?_⟩ (harc q₂.2 hq₂τ)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, hqC, hq⟩ := hgap x ⟨hx.1, hx.2.trans hx₂.2⟩
    refine ⟨q.2, ⟨zero_le, hle q hqC q₂ hq₂C (hq ▸ hq₂ ▸ hx.2.le)⟩, ?_⟩
    rw [← hq]
    exact hqC.2.2.symm

end W1

/-! ### The boundary-order theorem and Lemma W1 for ordered prefixes -/

section Ordered

/-- **Named input: the proper-completion boundary-order theorem** (Lemma G5, supplement §7, p. 493, for a common
seed, and its distinct-seed form, Aux. lemma 84; used in W1's proof, p. 530: "All contacts with second parameter
strictly below `t` have increasing coordinates, by the proper-completion boundary-order theorem", in W0b's,
p. 529, and in G9's, p. 501): two continuous injective proper curves in the closed upper half-plane, from real
seeds `γ₂ 0 ≤ γ₁ 0`, with `γ₂` in the full closed left side of `γ₁`, meet in increasing order in both
parametrizations ("their finite contacts occur in increasing order in both parametrizations. Noninitial real
contacts are allowed"). A complete curve `γ` is `IsProperCompletion γ 0 γ`. **Not proved in Lean** (its proof is
Aux. lemma 84's closed-Jordan-domain boundary-order argument, §7.2). -/
def OrderedContactOrderStatement : Prop :=
  ∀ γ₁ γ₂ : ℝ≥0 → ℂ, IsProperCompletion γ₁ 0 γ₁ → IsProperCompletion γ₂ 0 γ₂ →
    (γ₁ 0).im = 0 → (γ₂ 0).im = 0 → (γ₂ 0).re ≤ (γ₁ 0).re → range γ₂ ⊆ closedLeftSide γ₁ →
    ∀ s s' t t' : ℝ≥0, γ₁ s = γ₂ t → γ₁ s' = γ₂ t' → s < s' → t < t'

/-- A completed curve is its own completion from time `0`. -/
theorem isProperCompletion_self_zero {γ γ' : ℝ≥0 → ℂ} {a : ℝ≥0} (h : IsProperCompletion γ a γ') :
    IsProperCompletion γ' 0 γ' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ _ => rfl⟩

/-- **The increasing earlier contacts of W1** (p. 530) from the boundary-order theorem: if `α([0, A])` and every
`β([0, v])`, `v < t`, have ordered proper completions from real seeds `β 0 ≤ α 0`, the contacts with second
parameter below `t` are increasing. -/
theorem earlierContactsIncreasing_of_contactOrder (hord : OrderedContactOrderStatement)
    {α β : ℝ≥0 → ℂ} {A t : ℝ≥0} (hα0 : (α 0).im = 0) (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re)
    (hE : ∀ v < t, HasOrderedProperCompletions α A β v) : EarlierContactsIncreasing α A β t := by
  intro p hp q hq hpt hqt hpq
  obtain ⟨α', β', hα', hβ', hside⟩ := hE (max p.2 q.2) (max_lt hpt hqt)
  have e0α : α' 0 = α 0 := hα'.2.2.2.2 0 zero_le
  have e0β : β' 0 = β 0 := hβ'.2.2.2.2 0 zero_le
  refine hord α' β' (isProperCompletion_self_zero hα') (isProperCompletion_self_zero hβ')
    (by rw [e0α]; exact hα0) (by rw [e0β]; exact hβ0) (by rw [e0α, e0β]; exact hseed) hside
    p.1 q.1 p.2 q.2 ?_ ?_ hpq
  · rw [hα'.2.2.2.2 _ hp.1.2, hβ'.2.2.2.2 _ (le_max_left _ _), hp.2.2]
  · rw [hα'.2.2.2.2 _ hq.1.2, hβ'.2.2.2.2 _ (le_max_right _ _), hq.2.2]

/-- **Lemma W1** (incoming rational cuts for a backwards contact, pp. 529–530), its order-theoretic content for
ordered prefixes: under `𝓔(α([0, A]), β([0, v]))` for every `v < t` (which gives continuity and injectivity of the
earlier prefixes), continuity and injectivity of `β` on `[0, t]`, and the increasing earlier contacts, the cuts of
`w1_cuts` exist and moreover (item 1) the old pair `α([0, r])`, `β([0, s])` has ordered proper completions ("by
restriction of a pair with second parameter strictly between `s` and `t`"). -/
theorem w1_cuts_of_ordered {α β : ℝ≥0 → ℂ} {A t : ℝ≥0} (hE : ∀ v < t, HasOrderedProperCompletions α A β v)
    (ht : 0 < t) (hβ : ContinuousOn β (Icc 0 t)) (hβi : InjOn β (Icc 0 t))
    (hinc : EarlierContactsIncreasing α A β t)
    {a b₀ v₀ : ℝ≥0} (ha0 : 0 < a) (ha : a ≤ A) (hp : α a = β t) (hab : a < b₀) (hb₀ : b₀ ≤ A)
    (hv₀ : v₀ < t) (hq₀ : α b₀ = β v₀) (hβ0 : ∀ x ∈ Icc 0 A, α x = β 0 → x = 0)
    {R S : Set ℝ≥0} (hR : Dense R) (hS : Dense S) :
    ∃ r s b v : ℝ≥0, r ∈ R ∧ s ∈ S ∧ r < a ∧ a < b ∧ b ≤ A ∧ s < v ∧ v < t ∧ α b = β v ∧
      HasOrderedProperCompletions α r β s ∧ α r ≠ β s ∧
      (∀ x ∈ Icc r b, ∀ y ∈ Icc s t, α x = β y → (x = a ∧ y = t) ∨ (x = b ∧ y = v)) ∧
      Disjoint (α '' Icc r a) (β '' Icc s v) ∧
      Disjoint (α '' Ioc r b) (β '' Icc 0 s) ∧ Disjoint (β '' Ioc s t) (α '' Icc 0 r) ∧
      Disjoint (α '' Ioc r b) (α '' Icc 0 r) ∧ Disjoint (β '' Ioc s t) (β '' Icc 0 s) := by
  have hE0 := hE 0 ht
  obtain ⟨r, s, b, v, hrR, hsS, hra, hab', hbA, hsv, hvt, hbv, hne, hbox, h1, h2, h3, h4, h5⟩ :=
    w1_cuts (HasOrderedProperCompletions.continuousOn_left hE0) hβ
      (HasOrderedProperCompletions.injOn_left hE0) hβi hinc ha0 ha hp hab hb₀ hv₀ hq₀ hβ0 hR hS
  exact ⟨r, s, b, v, hrR, hsS, hra, hab', hbA, hsv, hvt, hbv,
    HasOrderedProperCompletions.mono (hE s (hsv.trans hvt)) (hra.le.trans ha) le_rfl,
    hne, hbox, h1, h2, h3, h4, h5⟩

end Ordered

end Supp9

end InteractingSLE
