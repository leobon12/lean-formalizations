/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S10Contact
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions

/-!
# Supplement §10, Lemma W6: contact order through finite terminal endpoints (deterministic steps)

Packet PROVE-SUPP10 (specification supplement §10, `source/spec/p529-576.md`, p. 537). Lemma W6: "Let two maximal
canonical finite-word flows from one real seed have distinct angles and admissible initial seed groups. Their finite
common points occur in increasing parameter order, including a common point at a finite continuation threshold of
either path." Its proof has three steps; the first two are deterministic and are proved here.

1. **Strict contacts** (`contacts_strict_increasing_of_completions`): "Every pair of strict prefixes has ordered
   proper completions by W5. The contact-order theorem G5 for these completions therefore orders every contact
   whose two parameters are strictly below their lifetimes." Lemma G5 (supplement §7.5, p. 494) is a deterministic
   statement of another section, not in Lean yet; it enters as the named input `G5Statement`, stated exactly
   (curves from `0`). The seeds here are at a common real point `x`, so the curves are translated
   (`closedLeftSide_add_real`).
2. **The endpoint cases** (`contactsIncreasing_of_strict_of_frontier`). A remaining reversed pair uses a finite
   threshold: either an edge contact reverses a strict-interior contact, or two distinct edge contacts reverse one
   another. These are exactly the alternatives of Lemma W2a (supplement §9, p. 533), whose conclusion on a
   rectangle `[0, A] × [0, B]` is the predicate `NoReversedFrontierPair`. W6's own deterministic analysis of the
   two-edge case (the earlier contacts lie in `[0, a) × [0, b)`, are compact, and admit rational cuts with an empty
   fresh lower rectangle avoiding both old prefixes) is `exists_cuts_of_reversed_edges`.
3. The exclusion of those configurations is probabilistic (W1–W2, and G7 with first-contact 7.7); see
   `S10Main.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp10

open Sec7

/-! ### Lemma G5 (named input) and translation of the closed left side -/

/-- **Named input: Lemma G5** (same-seed contact order allowing real contacts; supplement §7.5, p. 494): "Let
`γ₁, γ₂` be continuous injective proper curves from `0` to `∞` in the closed upper half-plane. Suppose `γ₂` is
contained in the full closed left Jordan side of `γ₁`, defined by closing the first curve along the lower vertical
ray. Then their finite contacts occur in increasing order in both parametrizations. Noninitial real contacts are
allowed." A continuous injective proper curve in the closed upper half-plane is `IsProperCompletion γ 0 γ`
(frozen W0 carrier). Deterministic; its proof is Aux. lemma 84's closed-Jordan-domain boundary order (§7.2). -/
def G5Statement : Prop :=
  ∀ γ₁ γ₂ : ℝ≥0 → ℂ, IsProperCompletion γ₁ 0 γ₁ → IsProperCompletion γ₂ 0 γ₂ → γ₁ 0 = 0 → γ₂ 0 = 0 →
    range γ₂ ⊆ closedLeftSide γ₁ →
    ∀ s s' t t' : ℝ≥0, γ₁ s = γ₂ t → γ₁ s' = γ₂ t' → (s < s' ↔ t < t')

/-- Translating a curve by a real number translates its seed-ray closure. -/
theorem seedRayClosure_add_real (γ : ℝ≥0 → ℂ) (x : ℝ) :
    seedRayClosure (fun t => γ t + x) = (· + (x : ℂ)) '' seedRayClosure γ := by
  unfold seedRayClosure
  rw [image_union, ← range_comp]
  congr 1
  ext z
  simp only [mem_ofPred_eq, mem_image, Complex.add_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨z - x, ⟨?_, ?_⟩, by ring⟩
    · simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    · simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact h2
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
    exact ⟨by rw [h1], h2⟩

/-- Translating a curve by a real number translates its full closed left Jordan side. -/
theorem closedLeftSide_add_real (γ : ℝ≥0 → ℂ) (x : ℝ) :
    closedLeftSide (fun t => γ t + x) = (· + (x : ℂ)) '' closedLeftSide γ := by
  set Φ := Homeomorph.addRight (x : ℂ) with hΦ
  have hS : (Φ : ℂ → ℂ) '' seedRayClosure γ = seedRayClosure (fun t => γ t + x) :=
    (seedRayClosure_add_real γ x).symm
  set p : ℂ := γ 0 - 1 - Complex.I with hp
  have hcompl : (Φ : ℂ → ℂ) '' (seedRayClosure γ)ᶜ = (seedRayClosure (fun t => γ t + x))ᶜ := by
    rw [← hS]; exact Φ.toEquiv.image_compl _
  have hΦp : Φ p = (fun t => γ t + (x : ℂ)) 0 - 1 - Complex.I := by
    simp only [hΦ, Homeomorph.coe_addRight, hp]; ring
  unfold closedLeftSide
  rw [image_union]
  congr 1
  · by_cases hpS : p ∈ (seedRayClosure γ)ᶜ
    · have h := Φ.image_connectedComponentIn hpS
      rw [hcompl, hΦp] at h
      exact h.symm
    · have hpS' : (fun t => γ t + (x : ℂ)) 0 - 1 - Complex.I ∉ (seedRayClosure (fun t => γ t + x))ᶜ := by
        rw [← hΦp, ← hcompl]
        rintro ⟨w, hw, hwp⟩
        exact hpS (Φ.injective hwp ▸ hw)
      rw [connectedComponentIn_eq_empty hpS', connectedComponentIn_eq_empty hpS, image_empty]
  · exact hS.symm

/-- `IsProperCompletion` is preserved by a real translation of both the prefix and its completion. -/
theorem IsProperCompletion.sub_real {γ γ' : ℝ≥0 → ℂ} {a : ℝ≥0} (h : IsProperCompletion γ a γ') (x : ℝ) :
    IsProperCompletion (fun t => γ t + (-x : ℝ)) a (fun t => γ' t + (-x : ℝ)) := by
  obtain ⟨hc, hi, him, hp, he⟩ := h
  refine ⟨hc.add continuous_const, fun s t hst => hi (by simpa using hst), fun t => ?_, ?_,
    fun t ht => by simp only [he t ht]⟩
  · simp only [Complex.add_im, Complex.ofReal_im, add_zero]; exact him t
  · refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖((-x : ℝ) : ℂ)‖) hp)
    have := norm_sub_norm_le (γ' t) (-((-x : ℝ) : ℂ))
    simp only [sub_neg_eq_add, norm_neg] at this
    show ‖γ' t‖ + -‖((-x : ℝ) : ℂ)‖ ≤ ‖γ' t + ((-x : ℝ) : ℂ)‖
    linarith

/-- A finite parameter strictly below a finite lifetime is strictly below its `toNNReal`. -/
theorem lt_toNNReal_of_coe_lt {s : ℝ≥0} {T : ℝ≥0∞} (h : T ≠ ⊤) (hs : (s : ℝ≥0∞) < T) :
    s < T.toNNReal := by
  rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal h]; exact hs

/-! ### Step 1: strict contacts are increasing -/

/-- **Lemma W6, step 1** (p. 537): if every pair of strict prefixes of `α`, `β` (common real seed `x`) has ordered
proper completions (the conclusion of W5), then by G5 every two contacts with parameters strictly below the lifetimes
are increasing in both parametrizations. -/
theorem contacts_strict_increasing_of_completions (hG5 : G5Statement) {α β : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0∞}
    {x : ℝ} (hα0 : α 0 = x) (hβ0 : β 0 = x)
    (hord : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < T₁ → (c : ℝ≥0∞) < T₂ → HasOrderedProperCompletions α a β c)
    {s s' t t' : ℝ≥0} (hs : (s : ℝ≥0∞) < T₁) (hs' : (s' : ℝ≥0∞) < T₁) (ht : (t : ℝ≥0∞) < T₂)
    (ht' : (t' : ℝ≥0∞) < T₂) (hst : α s = β t) (hst' : α s' = β t') : s < s' ↔ t < t' := by
  have ha : ((max s s' : ℝ≥0) : ℝ≥0∞) < T₁ := by rw [ENNReal.coe_max]; exact max_lt hs hs'
  have hc : ((max t t' : ℝ≥0) : ℝ≥0∞) < T₂ := by rw [ENNReal.coe_max]; exact max_lt ht ht'
  obtain ⟨α', β', hα', hβ', hsub⟩ := hord _ _ ha hc
  have hα'0 : α' 0 = x := (hα'.2.2.2.2 0 zero_le).trans hα0
  have hβ'0 : β' 0 = x := (hβ'.2.2.2.2 0 zero_le).trans hβ0
  set γ₁ : ℝ≥0 → ℂ := fun u => α' u + ((-x : ℝ) : ℂ) with hγ₁
  set γ₂ : ℝ≥0 → ℂ := fun u => β' u + ((-x : ℝ) : ℂ) with hγ₂
  have hp₁ : IsProperCompletion γ₁ 0 γ₁ := by
    obtain ⟨c, i, im, p, -⟩ := IsProperCompletion.sub_real hα' x
    exact ⟨c, i, im, p, fun _ _ => rfl⟩
  have hp₂ : IsProperCompletion γ₂ 0 γ₂ := by
    obtain ⟨c, i, im, p, -⟩ := IsProperCompletion.sub_real hβ' x
    exact ⟨c, i, im, p, fun _ _ => rfl⟩
  have h0₁ : γ₁ 0 = 0 := by simp only [hγ₁, hα'0, Complex.ofReal_neg, add_neg_cancel]
  have h0₂ : γ₂ 0 = 0 := by simp only [hγ₂, hβ'0, Complex.ofReal_neg, add_neg_cancel]
  have hsub' : range γ₂ ⊆ closedLeftSide γ₁ := by
    rw [hγ₁, closedLeftSide_add_real]
    rintro _ ⟨u, rfl⟩
    exact ⟨β' u, hsub ⟨u, rfl⟩, rfl⟩
  have e₁ : ∀ u ≤ max s s', γ₁ u = α u + ((-x : ℝ) : ℂ) := fun u hu => by
    simp only [hγ₁, hα'.2.2.2.2 u hu]
  have e₂ : ∀ u ≤ max t t', γ₂ u = β u + ((-x : ℝ) : ℂ) := fun u hu => by
    simp only [hγ₂, hβ'.2.2.2.2 u hu]
  refine hG5 γ₁ γ₂ hp₁ hp₂ h0₁ h0₂ hsub' s s' t t' ?_ ?_
  · rw [e₁ s (le_max_left _ _), e₂ t (le_max_left _ _), hst]
  · rw [e₁ s' (le_max_right _ _), e₂ t' (le_max_right _ _), hst']

/-- **Named input: Aux. lemma 84** (contact order for actual proper one-sided curves; §7.2, p. 298): "Let `α̂, β̂`
be continuous simple proper curves in `closure ℍ` from `x₁, x₂` to infinity, where `x₂ < x₁`. Suppose that
`β̂ ⊆ closure 𝓛_α̂`. Then their common points are encountered in the same order: if `α̂(u_j) = β̂(v_j)` for
`j = 1, 2` and `u₁ < u₂`, then `v₁ < v₂`." Deterministic; it is the distinct-seed form of the
"proper-completion boundary-order theorem" (W1's proof, p. 530) whose one-seed form is G5. -/
def Aux84Statement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (x₁ x₂ : ℝ), x₂ < x₁ → IsProperCompletion α 0 α → IsProperCompletion β 0 β →
    α 0 = x₁ → β 0 = x₂ → range β ⊆ closedLeftSide α →
    ∀ u₁ u₂ v₁ v₂ : ℝ≥0, α u₁ = β v₁ → α u₂ = β v₂ → u₁ < u₂ → v₁ < v₂

/-- **Strict contacts, ordered distinct seeds** (W1's proof, p. 530: "All contacts with second parameter strictly
below `t` have increasing coordinates, by the proper-completion boundary-order theorem"): if every pair of strict
prefixes of `α` (seed `x₁`) and `β` (seed `x₂ < x₁`) has ordered proper completions, then by Aux. lemma 84 every two
contacts with parameters strictly below the lifetimes are increasing. -/
theorem contacts_strict_increasing_of_completions_of_lt (h84 : Aux84Statement) {α β : ℝ≥0 → ℂ}
    {T₁ T₂ : ℝ≥0∞} {x₁ x₂ : ℝ} (hx : x₂ < x₁) (hα0 : α 0 = x₁) (hβ0 : β 0 = x₂)
    (hord : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < T₁ → (c : ℝ≥0∞) < T₂ → HasOrderedProperCompletions α a β c)
    {s s' t t' : ℝ≥0} (hs : (s : ℝ≥0∞) < T₁) (hs' : (s' : ℝ≥0∞) < T₁) (ht : (t : ℝ≥0∞) < T₂)
    (ht' : (t' : ℝ≥0∞) < T₂) (hst : α s = β t) (hst' : α s' = β t') (hlt : s < s') : t < t' := by
  have ha : ((max s s' : ℝ≥0) : ℝ≥0∞) < T₁ := by rw [ENNReal.coe_max]; exact max_lt hs hs'
  have hc : ((max t t' : ℝ≥0) : ℝ≥0∞) < T₂ := by rw [ENNReal.coe_max]; exact max_lt ht ht'
  obtain ⟨α', β', hα', hβ', hsub⟩ := hord _ _ ha hc
  have hp₁ : IsProperCompletion α' 0 α' := ⟨hα'.1, hα'.2.1, hα'.2.2.1, hα'.2.2.2.1, fun _ _ => rfl⟩
  have hp₂ : IsProperCompletion β' 0 β' := ⟨hβ'.1, hβ'.2.1, hβ'.2.2.1, hβ'.2.2.2.1, fun _ _ => rfl⟩
  refine h84 α' β' x₁ x₂ hx hp₁ hp₂ ((hα'.2.2.2.2 0 zero_le).trans hα0)
    ((hβ'.2.2.2.2 0 zero_le).trans hβ0) hsub s s' t t' ?_ ?_ hlt
  · rw [hα'.2.2.2.2 s (le_max_left _ _), hβ'.2.2.2.2 t (le_max_left _ _), hst]
  · rw [hα'.2.2.2.2 s' (le_max_right _ _), hβ'.2.2.2.2 t' (le_max_right _ _), hst']

/-! ### Step 2: the endpoint cases -/

/-- **The conclusion of Lemma W2a** (supplement §9, p. 533) on the rectangle `[0, A] × [0, B]`: "The new contacts on
its top or right edge cannot reverse the increasing order of the contacts in its strict interior, nor can the two new
edge contacts be distinct and reverse one another." A top-edge contact `(a, B)` reverses a strict-interior contact
`(b, v)` (`b < A`, `v < B`) iff `a < b`; a right-edge contact `(A, b)` reverses a strict-interior contact `(a, v)`
iff `b < v`; two edge contacts `(a, B)`, `(A, b)` at distinct points reverse one another iff `a < A` and `b < B`. -/
def NoReversedFrontierPair (α : ℝ≥0 → ℂ) (A : ℝ≥0) (β : ℝ≥0 → ℂ) (B : ℝ≥0) : Prop :=
  (∀ a b v : ℝ≥0, a ≤ A → b < A → v < B → α a = β B → α b = β v → ¬ a < b) ∧
    (∀ b a v : ℝ≥0, b ≤ B → a < A → v < B → α A = β b → α a = β v → ¬ b < v) ∧
    ∀ a b : ℝ≥0, a < A → b < B → α a = β B → α A = β b → α a ≠ α A → False

/-- **Lemma W6, step 2** (p. 537): if the strict contacts are increasing and on every finite rectangle inside the
available ranges no frontier pair is reversed (W2a), then all finite-parameter contacts, finite thresholds included,
are increasing. The cases: a reversed pair with an edge contact either reverses a strict-interior contact
(the edge-versus-interior case, "excluded by W1–W2"), or consists of two edge contacts `(a, T₂)` and `(T₁, b)`
(the two-threshold case, "First-contact 7.7 contradicts the displayed empty lower rectangle"). -/
theorem contactsIncreasing_of_strict_of_frontier {α β : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0∞}
    (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁})
    (hstrict : ∀ s s' t t' : ℝ≥0, (s : ℝ≥0∞) < T₁ → (s' : ℝ≥0∞) < T₁ → (t : ℝ≥0∞) < T₂ →
      (t' : ℝ≥0∞) < T₂ → α s = β t → α s' = β t' → s < s' → t < t')
    (hfront : ∀ A B : ℝ≥0, (A : ℝ≥0∞) ≤ T₁ → (B : ℝ≥0∞) ≤ T₂ → NoReversedFrontierPair α A β B) :
    ContactsIncreasing α T₁ β T₂ := by
  rintro ⟨s, t⟩ ⟨-, hsT, -, htT, hst⟩ ⟨s', t'⟩ ⟨-, hs'T, -, ht'T, hst'⟩ (hlt : s < s')
  show t < t'
  have hsT' : (s : ℝ≥0∞) < T₁ := (ENNReal.coe_lt_coe.mpr hlt).trans_le hs'T
  -- `t ≠ t'`, by injectivity
  have htt' : t ≠ t' := by
    intro h
    have : s = s' := hαi hsT hs'T (by rw [hst, hst', h])
    exact hlt.ne this
  -- the main case split
  rcases (le_iff_lt_or_eq.mp ht'T) with ht'lt | ht'eq
  · rcases (le_iff_lt_or_eq.mp htT) with htlt | hteq
    · rcases (le_iff_lt_or_eq.mp hs'T) with hs'lt | hs'eq
      · exact hstrict s s' t t' hsT' hs'lt htlt ht'lt hst hst' hlt
      · -- `(T₁, t')` is a right-edge contact, `(s, t)` strict: take `B` finite above `t, t'`
        set A : ℝ≥0 := s' with hA
        obtain ⟨B, hBT, htB, ht'B⟩ : ∃ B : ℝ≥0, (B : ℝ≥0∞) ≤ T₂ ∧ t < B ∧ t' < B := by
          rcases eq_or_ne T₂ ⊤ with h | h
          · exact ⟨max t t' + 1, by rw [h]; exact le_top,
              lt_of_le_of_lt (le_max_left _ _) (lt_add_one _),
              lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)⟩
          · refine ⟨T₂.toNNReal, ENNReal.coe_toNNReal_le_self, ?_, ?_⟩
            · exact lt_toNNReal_of_coe_lt h  htlt
            · exact lt_toNNReal_of_coe_lt h  ht'lt
        have hle : t ≤ t' := not_lt.mp ((hfront A B hs'eq.le hBT).2.1 t' s t ht'B.le hlt htB hst' hst)
        exact lt_of_le_of_ne hle htt'
    · -- `t = T₂` and `t' < T₂`: a top-edge contact `(s, T₂)` before `(s', t')`
      exfalso
      set B : ℝ≥0 := t with hB
      rcases (le_iff_lt_or_eq.mp hs'T) with hs'lt | hs'eq
      · obtain ⟨A, hAT, hsA, hs'A⟩ : ∃ A : ℝ≥0, (A : ℝ≥0∞) ≤ T₁ ∧ s ≤ A ∧ s' < A := by
          rcases eq_or_ne T₁ ⊤ with h | h
          · exact ⟨s' + 1, by rw [h]; exact le_top, hlt.le.trans (le_add_of_nonneg_right zero_le),
              lt_add_one _⟩
          · have hs'A : s' < T₁.toNNReal := lt_toNNReal_of_coe_lt h  hs'lt
            exact ⟨T₁.toNNReal, ENNReal.coe_toNNReal_le_self, hlt.le.trans hs'A.le, hs'A⟩
        have ht'B : t' < B := ENNReal.coe_lt_coe.mp (hteq ▸ ht'lt)
        exact (hfront A B hAT hteq.le).1 s s' t' hsA hs'A ht'B hst hst' hlt
      · have ht'B : t' < B := ENNReal.coe_lt_coe.mp (hteq ▸ ht'lt)
        have hne : α s ≠ α s' := fun h => hlt.ne (hαi hsT hs'T h)
        exact (hfront s' B hs'eq.le hteq.le).2.2 s t' hlt ht'B hst hst' hne
  · -- `t' = T₂`: then `t < t'` as `t ≤ T₂` and `t ≠ t'`
    have : (t : ℝ≥0∞) < t' := lt_of_le_of_ne (ht'eq ▸ htT) (by exact_mod_cast htt')
    exact ENNReal.coe_lt_coe.mp this

/-- A rational number strictly between two nonnegative reals, as an `ℝ≥0`. -/
theorem exists_rat_nnreal_btwn {u v : ℝ≥0} (h : u < v) :
    ∃ r : ℝ≥0, u < r ∧ r < v ∧ ∃ q : ℚ, (r : ℝ) = q := by
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show (u : ℝ) < v from h)
  have hq0 : (0 : ℝ) ≤ q := u.2.trans hq₁.le
  exact ⟨⟨q, hq0⟩, hq₁, hq₂, q, rfl⟩

/-- **Lemma W6, the two-threshold configuration** (p. 537). Let `α|[0, A]`, `β|[0, B]` be continuous and injective,
with edge contacts `p = α(a) = β(B)` and `q = α(A) = β(b)`, `a < A`, `b < B`, neither reversing a strict-interior
contact: every strict-interior contact `(x, y)` has `x < a` and `y < b`. "The earlier contact set consequently lies
in the strict rectangle `[0, a) × [0, b)` [and] is compact […]. Choose rational interior cuts `r ∈ (a₋, a)` and
`s ∈ (b₋, b)`; if the earlier set is empty, use the initial parameters as the lower ends. The two fresh terminal
histories contain `p` and `q` but satisfy `α([r, a]) ∩ β([s, b]) = ∅`. They avoid both old prefixes, since all earlier
contacts precede both cuts." The cuts are rational, above every earlier contact, strictly below `a`, `b` when there
is an earlier contact, and the fresh histories `α([r, A])`, `β([s, B])` avoid the old prefixes `β([0, s))`,
`α([0, r))`. -/
theorem exists_cuts_of_reversed_edges {α β : ℝ≥0 → ℂ} {A B a b : ℝ≥0}
    (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B)) (haA : a < A) (hbB : b < B)
    (hp : α a = β B) (hq : α A = β b)
    (hearly : ∀ x y : ℝ≥0, x < A → y < B → α x = β y → x < a ∧ y < b) :
    ∃ r s : ℝ≥0, (∃ q : ℚ, (r : ℝ) = q) ∧ (∃ q : ℚ, (s : ℝ) = q) ∧ r ≤ a ∧ s ≤ b ∧
      (∀ x y : ℝ≥0, x < A → y < B → α x = β y → x < r ∧ y < s) ∧
      ((∃ x y : ℝ≥0, x < A ∧ y < B ∧ α x = β y) → r < a ∧ s < b) ∧
      (∀ x y : ℝ≥0, r ≤ x → x ≤ a → s ≤ y → y ≤ b → α x ≠ β y) ∧
      (∀ x y : ℝ≥0, r ≤ x → x ≤ A → y < s → α x ≠ β y) ∧
      (∀ x y : ℝ≥0, x < r → s ≤ y → y ≤ B → α x ≠ β y) := by
  set K := (Icc 0 a ×ˢ Icc 0 b) ∩ {p : ℝ≥0 × ℝ≥0 | α p.1 = β p.2} with hKdef
  have hK : IsCompact K := isCompact_contacts_Icc (hα.mono (Icc_subset_Icc le_rfl haA.le))
    (hβ.mono (Icc_subset_Icc le_rfl hbB.le))
  -- the strict-interior contacts are exactly the points of `K`
  have hmemK : ∀ x y : ℝ≥0, x < A → y < B → α x = β y → (x, y) ∈ K := fun x y hx hy hxy =>
    ⟨⟨⟨zero_le, (hearly x y hx hy hxy).1.le⟩, ⟨zero_le, (hearly x y hx hy hxy).2.le⟩⟩, hxy⟩
  have hKstrict : ∀ p ∈ K, p.1 < a ∧ p.2 < b := fun p hp =>
    hearly p.1 p.2 (hp.1.1.2.trans_lt haA) (hp.1.2.2.trans_lt hbB) hp.2
  -- the cuts
  obtain ⟨r, s, hrq, hsq, hra, hsb, habove, hlt⟩ : ∃ r s : ℝ≥0, (∃ q : ℚ, (r : ℝ) = q) ∧
      (∃ q : ℚ, (s : ℝ) = q) ∧ r ≤ a ∧ s ≤ b ∧ (∀ p ∈ K, p.1 < r ∧ p.2 < s) ∧
      (K.Nonempty → r < a ∧ s < b) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨0, 0, ⟨0, by simp⟩, ⟨0, by simp⟩, zero_le, zero_le, ?_, ?_⟩
      · intro p hp; rw [hKe] at hp; exact absurd hp (notMem_empty p)
      · intro h; rw [hKe] at h; exact absurd h not_nonempty_empty
    · obtain ⟨p₁, hp₁, hmax₁⟩ := hK.exists_isMaxOn hKne continuous_fst.continuousOn
      obtain ⟨p₂, hp₂, hmax₂⟩ := hK.exists_isMaxOn hKne continuous_snd.continuousOn
      obtain ⟨r, hr₁, hr₂, hrq⟩ := exists_rat_nnreal_btwn (hKstrict p₁ hp₁).1
      obtain ⟨s, hs₁, hs₂, hsq⟩ := exists_rat_nnreal_btwn (hKstrict p₂ hp₂).2
      exact ⟨r, s, hrq, hsq, hr₂.le, hs₂.le,
        fun p hp => ⟨(show p.1 ≤ p₁.1 from hmax₁ hp).trans_lt hr₁,
          (show p.2 ≤ p₂.2 from hmax₂ hp).trans_lt hs₁⟩, fun _ => ⟨hr₂, hs₂⟩⟩
  refine ⟨r, s, hrq, hsq, hra, hsb, fun x y hx hy hxy => habove _ (hmemK x y hx hy hxy),
    fun ⟨x, y, hx, hy, hxy⟩ => hlt ⟨_, hmemK x y hx hy hxy⟩, ?_, ?_, ?_⟩
  · intro x y hrx hxa hsy hyb hxy
    exact absurd hrx (not_le.mpr (habove (x, y) ⟨⟨⟨zero_le, hxa⟩, ⟨zero_le, hyb⟩⟩, hxy⟩).1)
  · intro x y hrx hxA hys hxy
    have hyB : y < B := (hys.trans_le hsb).trans hbB
    rcases hxA.lt_or_eq with hxA' | rfl
    · exact absurd hrx (not_le.mpr (habove _ (hmemK x y hxA' hyB hxy)).1)
    · have : y = b := hβi ⟨zero_le, hyB.le⟩ ⟨zero_le, hbB.le⟩ (by rw [← hxy, hq])
      exact absurd (this ▸ hys) (not_lt.mpr hsb)
  · intro x y hxr hsy hyB hxy
    have hxA : x < A := (hxr.trans_le hra).trans haA
    rcases hyB.lt_or_eq with hyB' | rfl
    · exact absurd hsy (not_le.mpr (habove _ (hmemK x y hxA hyB' hxy)).2)
    · have : x = a := hαi ⟨zero_le, hxA.le⟩ ⟨zero_le, haA.le⟩ (by rw [hxy, hp])
      exact absurd (this ▸ hxr) (not_lt.mpr hra)

/-- **Lemma W6** (p. 537), the source's derivation of the two-threshold configuration: at edge contacts `(a, B)`,
`(A, b)` neither of which reverses a strict-interior contact, "every strict-interior contact `(x, y)` must then
satisfy `x < a` and `y < b`. A value `x > a` or `y > b` is the edge-versus-interior case just excluded; equality
would repeat the physical point `p` on `β` or `q` on `α` before its endpoint, violating injectivity." -/
theorem early_of_noReversedFrontierPair {α β : ℝ≥0 → ℂ} {A B a b : ℝ≥0}
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B))
    (hfr : NoReversedFrontierPair α A β B) (haA : a ≤ A) (hbB : b ≤ B) (hp : α a = β B)
    (hq : α A = β b) : ∀ x y : ℝ≥0, x < A → y < B → α x = β y → x < a ∧ y < b := by
  intro x y hx hy hxy
  constructor
  · refine lt_of_le_of_ne (not_lt.mp (hfr.1 a x y haA hx hy hp hxy)) fun hxa => ?_
    have : y = B := hβi ⟨zero_le, hy.le⟩ ⟨zero_le, le_rfl⟩ (by rw [← hxy, hxa, hp])
    exact hy.ne this
  · refine lt_of_le_of_ne (not_lt.mp (hfr.2.1 b x y hbB hx hy hq hxy)) fun hyb => ?_
    have : x = A := hαi ⟨zero_le, hx.le⟩ ⟨zero_le, le_rfl⟩ (by rw [hxy, hyb, hq])
    exact hx.ne this

end Supp10

end InteractingSLE
