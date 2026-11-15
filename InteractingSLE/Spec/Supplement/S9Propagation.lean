/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9Contacts
import InteractingSLE.Spec.Sec7.InteractionProbLemma77

/-!
# Supplement §9: Theorem W5 (propagation of strict-prefix ordered completion)

Packet PROVE-SUPP9 (specification supplement §9, `source/spec/p529-576.md` L101–L180, pp. 533–536).

## The first-loss argument, pathwise

Theorem W5's proof fixes one sample, on "the common probability-one event for all rational own stopping pairs,
countable buffered localizations, marked kernels and local comparison conclusions" (p. 534), and then argues
deterministically. `forall_hasOrderedProperCompletions_of_firstLoss` is that deterministic argument, for two
curves `α`, `β` with available lifetimes `ζ₁`, `ζ₂`, from four pathwise properties:

* the initial order (`hinit`): for `0 < A < ζ₁`, `𝓔(α([0, A]), β([0, c₀]))` for some `c₀ > 0`;
* `ExtendsWithoutNewContact` — the conclusion of **Lemma W4** (p. 532) on this sample;
* `NoBackwardContact` — the conclusion of **Lemmas W1–W2** (pp. 529–531) as W5 uses it: "W1–W2 exclude any
  earlier common point with first parameter greater than `a`";
* `LocalCompletionAtContact` — the conclusion of the paragraphs "Incoming active rational cuts" and "The interior
  and real local frames" of W5's proof (pp. 534–536): at a contact `p = α(a) = β(τ)` reached in order, the locally
  enlarged prefixes have ordered proper completions.

The proof is the source's: let `τ` be the infimum of the failures of `E(b) = 𝓔(α([0, A]), β([0, b]))` (an initial
interval by heredity); `τ > 0` by the initial order; `β(τ)` lies on `α([0, A])`, since otherwise W4 extends past
`τ`; at `p = β(τ) = α(a)` the local frame gives `𝓔(α([0, a₊]), β([0, b₊]))`; if `a₊ ≥ A` restriction gives
`E(b₊)`, and otherwise the far suffix `α([a₊, A])` is disjoint from `β([0, τ])` (by W1–W2 and injectivity), hence
from `β([0, b'])` for some `b' > τ`, and W4a splices it back: `E(b')`, contradicting the choice of `τ`.

`initial_of_distinctSeeds` and `initial_of_commonSeed` derive the initial order from W4, as the source does: for
distinct seeds from W0a and the singleton base case (`hasOrderedProperCompletions_zero`, then G13a inside W4);
for a common seed from the local comparison at the seed (Aux. lemma 97, Proposition 7.4, G1) and W4a.
`noBackwardContact_of_not_isW1Configuration` derives `NoBackwardContact` from W2 ("the event described in W1 has
probability zero"), W0b (no common open subarc) and W0a (no visit of the other seed), as in W5's proof.
`ExtendsWithoutNewContact.splice` is **Corollary W4a** (p. 532).

## Theorem W5 on the frozen carriers

`w5Statement_of_inputs` proves the frozen-carrier statement `Theorem15.W5Statement` (the input of Theorem 1.5)
from Aux. lemma 25 and six §9 statements, each stated exactly on the frozen carriers with its page:
`W0aStatement`, `W0bStatement`, `W2Statement`, `W4Statement`, `W5CommonSeedStatement`, `W5LocalFrameStatement`.
These are **not proved in Lean** (they need the §7 comparison lemmas G3–G13a, Lemma 7.7 and conformal joint-chart
facts, none of which is in Lean); it is a conditional helper, recorded as the exact remaining obligation of W5.
`W0aStatement` is itself derived from Lemma G12 (§7, `G12FlowStatement`) by `w0aStatement_of_g12`: its weight
computation and the seed admissibility of a positive lifetime (`ae_seedWeights_of_isFlowLine`) are proved.

## Endpoint scope

`IsClosedStoppedOrdered` is the closed stopped-order relation at finite thresholds ("Strict lifetime and terminal
conventions", p. 533), and `ae_isClosedStoppedOrdered_of_w5` derives it from W5 by endpoint continuity ("Endpoint
scope of W5", p. 536).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp9

open Sec7

/-! ### Pathwise properties -/

/-- The conclusion of **Lemma W4** (extension without a new mutual contact, p. 532) for two curves with available
lifetimes: "Suppose `𝓔(α([0, a]), β([0, c]))` holds. Extend one or both original simple Loewner prefixes, within
their available lifetimes, without adding any new mutual contact. At the last old common point, every suffix which
was a singleton must either remain a singleton or have a positive initial portion certified […]. Then the enlarged
pair still satisfies `𝓔`." Here an extended prefix is required to have a nontrivial old suffix (its old endpoint is
not a contact), which covers the case "When both old suffixes were already nontrivial" and a fixed other path. -/
def ExtendsWithoutNewContact (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∀ a a' c c' : ℝ≥0, a ≤ a' → (a' : ℝ≥0∞) < ζ₁ → c ≤ c' → (c' : ℝ≥0∞) < ζ₂ →
    HasOrderedProperCompletions α a β c →
    (∀ x ∈ Icc 0 a', ∀ y ∈ Icc 0 c', α x = β y → x ≤ a ∧ y ≤ c) →
    (a < a' → α a ∉ β '' Icc 0 c) → (c < c' → β c ∉ α '' Icc 0 a) →
    HasOrderedProperCompletions α a' β c'

/-- The configuration of **Lemma W1** (pp. 529–530), whose probability is zero by **Lemma W2** (p. 530): prefixes
`α([0, A])`, `β([0, t])` "with their available finite endpoints included" (`A ≤ ζ₁`, `t ≤ ζ₂`), an ordered history
`𝓔(α([0, A]), β([0, v]))` for every `v < t`, a new contact `p = α(a) = β(t)` and an earlier contact
`q₀ = α(b₀) = β(v₀)` with `0 < a < b₀ ≤ A`, `v₀ < t`, no common open subarc before `t`, and `p` not an original
seed. -/
def IsW1Configuration (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∃ A t a b₀ v₀ : ℝ≥0, (A : ℝ≥0∞) ≤ ζ₁ ∧ (t : ℝ≥0∞) ≤ ζ₂ ∧
    (∀ v < t, HasOrderedProperCompletions α A β v) ∧ α a = β t ∧ α b₀ = β v₀ ∧
    0 < a ∧ a < b₀ ∧ b₀ ≤ A ∧ v₀ < t ∧ (∀ v < t, ¬ HasCommonOpenSubarc α A β v) ∧
    α a ≠ α 0 ∧ α a ≠ β 0

/-- No backwards contact (Theorem W5's proof, p. 534: "W1–W2 exclude any earlier common point with first parameter
greater than `a`"): after an ordered history up to `t`, a contact `α(a) = β(t)` has no earlier contact
`α(b₀) = β(v₀)`, `v₀ < t`, with `a < b₀ ≤ A`. -/
def NoBackwardContact (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∀ A a t b₀ v₀ : ℝ≥0, (A : ℝ≥0∞) < ζ₁ → (t : ℝ≥0∞) < ζ₂ → 0 < t →
    (∀ v < t, HasOrderedProperCompletions α A β v) → a ≤ A → α a = β t → a < b₀ → b₀ ≤ A → v₀ < t →
    α b₀ ≠ β v₀

/-- The conclusion of the local frames of Theorem W5's proof (pp. 534–536: "Incoming active rational cuts", "The
interior and real local frames", first sentence of "Splicing the rest of the current histories"): at a contact
`p = α(a) = β(τ)` with an ordered history `𝓔(α([0, a]), β([0, v]))` for `v < τ`, strictly before both lifetimes,
there are `a₊ > a`, `b₊ > τ` within the lifetimes with `𝓔(α([0, a₊]), β([0, b₊]))`. -/
def LocalCompletionAtContact (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∀ a τ : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (τ : ℝ≥0∞) < ζ₂ → 0 < τ → α a = β τ →
    (∀ v < τ, HasOrderedProperCompletions α a β v) →
    ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ∧
      HasOrderedProperCompletions α a₂ β b₂

/-! ### Elementary facts about available curves -/

section Curves

variable {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}

theorem isOpen_setOf_coe_lt (ζ : ℝ≥0∞) : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} :=
  isOpen_lt ENNReal.continuous_coe continuous_const

/-- A curve continuous on its available interval is continuous at every time strictly before the lifetime. -/
theorem continuousAt_of_coe_lt (hγ : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ ζ}) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < ζ) : ContinuousAt γ τ :=
  hγ.continuousAt (mem_of_superset ((isOpen_setOf_coe_lt ζ).mem_nhds hτ)
    fun t (h : (t : ℝ≥0∞) < ζ) => show (t : ℝ≥0∞) ≤ ζ from h.le)

/-- A finite available prefix has closed range. -/
theorem isClosed_image_Icc (hγ : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ ζ}) {a b : ℝ≥0}
    (hb : (b : ℝ≥0∞) ≤ ζ) : IsClosed (γ '' Icc a b) :=
  (isCompact_Icc.image_of_continuousOn
    (hγ.mono fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hb)).isClosed

/-- Right after an available time `τ < ζ`, the curve stays off a closed set it avoids at `τ`. -/
theorem exists_right_avoid (hγ : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ ζ}) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < ζ) {K : Set ℂ} (hK : IsClosed K) (hτK : γ τ ∉ K) :
    ∃ u : ℝ≥0, τ < u ∧ (u : ℝ≥0∞) < ζ ∧ ∀ t ∈ Icc τ u, γ t ∉ K := by
  have hev : ∀ᶠ t in 𝓝 τ, γ t ∉ K ∧ (t : ℝ≥0∞) < ζ :=
    ((continuousAt_of_coe_lt hγ hτ).eventually (hK.isOpen_compl.mem_nhds hτK)).and
      ((isOpen_setOf_coe_lt ζ).mem_nhds hτ)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 (nhdsWithin_le_nhds hev)
  exact ⟨u, hu, (hsub ⟨hu.le, le_rfl⟩).2, fun t ht => (hsub ht).1⟩

/-- Right before an available time `0 < τ < ζ`, the curve stays off a closed set it avoids at `τ`. -/
theorem exists_left_avoid (hγ : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ ζ}) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < ζ) (hτ0 : 0 < τ) {K : Set ℂ} (hK : IsClosed K) (hτK : γ τ ∉ K) :
    ∃ l : ℝ≥0, l < τ ∧ ∀ t ∈ Icc l τ, γ t ∉ K := by
  have hev : ∀ᶠ t in 𝓝 τ, γ t ∉ K :=
    (continuousAt_of_coe_lt hγ hτ).eventually (hK.isOpen_compl.mem_nhds hτK)
  obtain ⟨l', hl', hsub⟩ := exists_Ioc_subset_of_mem_nhds' hev hτ0
  obtain ⟨l, hl1, hl2⟩ := exists_between hl'.2
  exact ⟨l, hl2, fun t ht => hsub ⟨hl1.trans_le ht.1, ht.2⟩⟩

theorem mem_setOf_coe_le_of_le {a b : ℝ≥0} (hab : a ≤ b) (hb : (b : ℝ≥0∞) < ζ) :
    a ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} :=
  (ENNReal.coe_le_coe.2 hab).trans hb.le

end Curves

/-! ### Corollary W4a -/

section W4a

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- **Corollary W4a** (splicing back a long disjoint suffix, p. 532): "If a local comparison proves
`𝓔(α([0, a₊]), β([0, b]))`, and an additional available suffix `α([a₊, A])` is disjoint from the entire second
prefix, […] Then `𝓔(α([0, A]), β([0, b]))`. […] This is W4. […] The extended suffix was already nontrivial, and the
other path is kept fixed, so the extra cyclic-order hypothesis of W4 is satisfied." The source's condition that
`a₊` be after the last common point follows from the disjointness. -/
theorem ExtendsWithoutNewContact.splice (hW4 : ExtendsWithoutNewContact α ζ₁ β ζ₂) {a₂ A b : ℝ≥0}
    (haA : a₂ ≤ A) (hA : (A : ℝ≥0∞) < ζ₁) (hb : (b : ℝ≥0∞) < ζ₂)
    (hE : HasOrderedProperCompletions α a₂ β b) (hdisj : Disjoint (α '' Icc a₂ A) (β '' Icc 0 b)) :
    HasOrderedProperCompletions α A β b := by
  have hd := disjoint_image_image_iff.1 hdisj
  refine hW4 a₂ A b b haA hA le_rfl hb hE (fun x hx y hy hxy => ⟨not_lt.1 fun h => ?_, hy.2⟩)
    (fun _ ⟨y, hy, hye⟩ => hd a₂ ⟨le_rfl, haA⟩ y hy hye.symm) (fun h => absurd h (lt_irrefl _))
  exact hd x ⟨h.le, hx.2⟩ y hy hxy

end W4a

/-! ### The first-loss argument -/

section FirstLoss

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- **Theorem W5, the first-loss argument** (pp. 534–536), pathwise: from the initial order, W4, the exclusion of
backwards contacts (W1–W2) and the local frames, every pair of finite prefixes strictly before the lifetimes has
ordered proper completions. -/
theorem forall_hasOrderedProperCompletions_of_firstLoss
    (hαc : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hβc : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hinit : ∀ A : ℝ≥0, 0 < A → (A : ℝ≥0∞) < ζ₁ → 0 < ζ₂ →
      ∃ c₀ : ℝ≥0, 0 < c₀ ∧ (c₀ : ℝ≥0∞) < ζ₂ ∧ HasOrderedProperCompletions α A β c₀)
    (hW4 : ExtendsWithoutNewContact α ζ₁ β ζ₂) (hback : NoBackwardContact α ζ₁ β ζ₂)
    (hloc : LocalCompletionAtContact α ζ₁ β ζ₂) :
    ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c := by
  have main : ∀ A : ℝ≥0, 0 < A → (A : ℝ≥0∞) < ζ₁ → ∀ c : ℝ≥0, (c : ℝ≥0∞) < ζ₂ →
      HasOrderedProperCompletions α A β c := by
    intro A hA0 hA c hc
    by_contra hfail
    set F := {b : ℝ≥0 | ¬ HasOrderedProperCompletions α A β b} with hF_def
    have hFne : F.Nonempty := ⟨c, hfail⟩
    have hFbdd : BddBelow F := ⟨0, fun _ _ => zero_le⟩
    set τ := sInf F with hτ_def
    have hbelow : ∀ b < τ, HasOrderedProperCompletions α A β b := fun b hb =>
      not_not.1 (notMem_of_lt_csInf hb hFbdd)
    have habove : ∀ b, τ < b → ¬ HasOrderedProperCompletions α A β b := by
      intro b hb hE
      obtain ⟨f, hfF, hfb⟩ := exists_lt_of_csInf_lt hFne hb
      exact hfF (HasOrderedProperCompletions.mono_right hE hfb.le)
    have hτζ : (τ : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.2 (csInf_le hFbdd hfail)).trans_lt hc
    obtain ⟨c₀, hc₀, -, hEc₀⟩ := hinit A hA0 hA (lt_of_le_of_lt zero_le hτζ)
    have hτ0 : 0 < τ := lt_of_lt_of_le hc₀ (not_lt.1 fun h => habove c₀ h hEc₀)
    have hKA : IsClosed (α '' Icc 0 A) := isClosed_image_Icc hαc hA.le
    -- the first loss is a contact with the fixed first prefix
    have hmemA : β τ ∈ α '' Icc 0 A := by
      by_contra hnot
      obtain ⟨u, hτu, huζ, hu⟩ := exists_right_avoid hβc hτζ hKA hnot
      obtain ⟨l, hlτ, hl⟩ := exists_left_avoid hβc hτζ hτ0 hKA hnot
      have hoff : ∀ y ∈ Icc l u, β y ∉ α '' Icc 0 A := fun y hy => by
        rcases le_total y τ with h | h
        · exact hl y ⟨hy.1, h⟩
        · exact hu y ⟨h, hy.2⟩
      refine habove u hτu (hW4 A A l u le_rfl hA (hlτ.trans hτu).le huζ (hbelow l hlτ)
        (fun x hx y hy hxy => ⟨hx.2, not_lt.1 fun h => hoff y ⟨h.le, hy.2⟩ ⟨x, hx, hxy⟩⟩)
        (fun h => absurd h (lt_irrefl _)) (fun _ => hoff l ⟨le_rfl, (hlτ.trans hτu).le⟩))
    obtain ⟨a, haA, hpa⟩ := hmemA
    have haζ : (a : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.2 haA.2).trans_lt hA
    obtain ⟨a₂, b₂, haa, ha₂ζ, hτb, hb₂ζ, hE₂⟩ := hloc a τ haζ hτζ hτ0 hpa
      (fun v hv => HasOrderedProperCompletions.mono_left (hbelow v hv) haA.2)
    rcases le_or_gt A a₂ with hAa | hAa
    · exact habove b₂ hτb (HasOrderedProperCompletions.mono_left hE₂ hAa)
    -- splicing the far first suffix back
    have hdisj : ∀ x ∈ Icc a₂ A, ∀ y ∈ Icc 0 τ, α x ≠ β y := by
      intro x hx y hy hxy
      rcases hy.2.lt_or_eq with hyτ | hyτ
      · exact hback A a τ x y hA hτζ hτ0 hbelow haA.2 hpa (haa.trans_le hx.1) hx.2 hyτ hxy
      · have hxa : x = a := hαi (mem_setOf_coe_le_of_le hx.2 hA) (mem_setOf_coe_le_of_le haA.2 hA)
          (by rw [hxy, hyτ, hpa])
        exact absurd (hxa ▸ hx.1) (not_le.2 haa)
    have hK₂ : IsClosed (α '' Icc a₂ A) := isClosed_image_Icc hαc hA.le
    have hτK : β τ ∉ α '' Icc a₂ A := fun ⟨x, hx, hxe⟩ => hdisj x hx τ ⟨zero_le, le_rfl⟩ hxe
    obtain ⟨u, hτu, huζ, hu⟩ := exists_right_avoid hβc hτζ hK₂ hτK
    have hτb' : τ < min b₂ u := lt_min hτb hτu
    have hb'ζ : ((min b₂ u : ℝ≥0) : ℝ≥0∞) < ζ₂ :=
      (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt huζ
    refine habove _ hτb' (ExtendsWithoutNewContact.splice hW4 hAa.le hA hb'ζ
      (HasOrderedProperCompletions.mono_right hE₂ (min_le_left _ _)) ?_)
    refine disjoint_image_image_iff.2 fun x hx y hy hxy => ?_
    rcases le_total y τ with h | h
    · exact hdisj x hx y ⟨zero_le, h⟩ hxy
    · exact hu y ⟨h, hy.2.trans (min_le_right _ _)⟩ ⟨x, hx, hxy⟩
  intro a c ha hc
  obtain ⟨A, haA, hA⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ha
  have haA' : a < A := ENNReal.coe_lt_coe.1 haA
  exact HasOrderedProperCompletions.mono_left (main A (lt_of_le_of_lt zero_le haA') hA c hc) haA'.le

end FirstLoss

/-! ### The initial order and the exclusion of backwards contacts -/

section Derived

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

/-- **Theorem W5's proof, the initial order for distinct seeds** (p. 534): "For distinct seeds, W0a and
compactness give positive clearance between the whole fixed first prefix and the second seed. Sufficiently short
second prefixes are therefore disjoint from the whole first prefix, and G13a applies." G13a is used through W4 from
the two singleton prefixes ("If the original prefixes have no common point, neither do the enlarged prefixes. The
distinct-seed disjoint-arc completion theorem G13a applies", p. 532). -/
theorem initial_of_distinctSeeds (hαc : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hβc : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂}) (hW4 : ExtendsWithoutNewContact α ζ₁ β ζ₂)
    {x₁ x₂ : ℝ} (hx : x₂ < x₁) (hα0 : α 0 = x₁) (hβ0 : β 0 = x₂)
    (hvis : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → α s ≠ x₂) {A : ℝ≥0} (hA : (A : ℝ≥0∞) < ζ₁)
    (hζ₂ : 0 < ζ₂) :
    ∃ c₀ : ℝ≥0, 0 < c₀ ∧ (c₀ : ℝ≥0∞) < ζ₂ ∧ HasOrderedProperCompletions α A β c₀ := by
  have hK : IsClosed (α '' Icc 0 A) := isClosed_image_Icc hαc hA.le
  have h0 : β 0 ∉ α '' Icc 0 A := fun ⟨s, hs, hse⟩ =>
    hvis s (mem_setOf_coe_le_of_le hs.2 hA) (hse.trans hβ0)
  obtain ⟨u, hu0, huζ, hu⟩ := exists_right_avoid hβc (by rwa [ENNReal.coe_zero]) hK h0
  refine ⟨u, hu0, huζ, hW4 0 A 0 u zero_le hA zero_le huζ
    (hasOrderedProperCompletions_zero hα0 hβ0 hx.le) (fun x hx y hy hxy => absurd ⟨x, hx, hxy⟩ (hu y hy))
    (fun _ ⟨y, hy, hye⟩ => ?_) (fun _ ⟨x', hx', hxe⟩ => ?_)⟩
  · rw [le_antisymm hy.2 zero_le, hβ0, hα0] at hye
    exact (ne_of_lt hx) (Complex.ofReal_injective hye)
  · rw [le_antisymm hx'.2 zero_le, hα0, hβ0] at hxe
    exact (ne_of_lt hx) (Complex.ofReal_injective hxe).symm

/-- **Theorem W5's proof, the initial order for a common seed** (p. 534): from the local comparison at the seed
("the two original stopped prefixes have actual ordered proper completions", `hseed`), "Choose `a₀ ∈ (0, A)` so
small that the first prefix through `a₀` is within this comparison neighborhood. Injectivity gives positive
clearance between the common seed and `α([a₀/2, A])`. Take `b₀ > 0` so small that the second prefix through `b₀`
lies inside a smaller clearance neighborhood and inside the comparison neighborhood. […] W4a therefore restores the
entire first suffix through `A`." -/
theorem initial_of_commonSeed (hαc : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hβc : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂}) (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hW4 : ExtendsWithoutNewContact α ζ₁ β ζ₂) (h0 : α 0 = β 0)
    (hseed : 0 < ζ₁ → 0 < ζ₂ → ∃ a₀ c₀ : ℝ≥0, 0 < a₀ ∧ (a₀ : ℝ≥0∞) < ζ₁ ∧ 0 < c₀ ∧
      (c₀ : ℝ≥0∞) < ζ₂ ∧ HasOrderedProperCompletions α a₀ β c₀)
    {A : ℝ≥0} (hA0 : 0 < A) (hA : (A : ℝ≥0∞) < ζ₁) (hζ₂ : 0 < ζ₂) :
    ∃ c₀ : ℝ≥0, 0 < c₀ ∧ (c₀ : ℝ≥0∞) < ζ₂ ∧ HasOrderedProperCompletions α A β c₀ := by
  obtain ⟨a₀, c₀, ha₀, -, hc₀, -, hE⟩ := hseed (lt_of_le_of_lt zero_le hA) hζ₂
  have ha₁ : 0 < min a₀ A := lt_min ha₀ hA0
  have hE₁ := HasOrderedProperCompletions.mono_left hE (min_le_left a₀ A)
  have hK : IsClosed (α '' Icc (min a₀ A / 2) A) := isClosed_image_Icc hαc hA.le
  have h0K : β 0 ∉ α '' Icc (min a₀ A / 2) A := by
    rintro ⟨s, hs, hse⟩
    have hs0 : s = 0 := hαi (mem_setOf_coe_le_of_le hs.2 hA) (mem_setOf_coe_le_of_le zero_le hA)
      (hse.trans h0.symm)
    exact absurd (hs0 ▸ hs.1) (not_le.2 (half_pos ha₁))
  obtain ⟨u, hu0, huζ, hu⟩ := exists_right_avoid hβc (by rwa [ENNReal.coe_zero]) hK h0K
  have hc₁ζ : ((min c₀ u : ℝ≥0) : ℝ≥0∞) < ζ₂ :=
    (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt huζ
  refine ⟨min c₀ u, lt_min hc₀ hu0, hc₁ζ, ExtendsWithoutNewContact.splice hW4 (min_le_right _ _) hA hc₁ζ
    (HasOrderedProperCompletions.mono_right hE₁ (min_le_left _ _)) ?_⟩
  refine disjoint_image_image_iff.2 fun x hx y hy hxy => hu y ⟨zero_le, hy.2.trans (min_le_right _ _)⟩
    ⟨x, ⟨(half_le_self (zero_le : (0 : ℝ≥0) ≤ min a₀ A)).trans hx.1, hx.2⟩, hxy⟩

/-- **The exclusion of backwards contacts** used in Theorem W5's proof (p. 534: "W1–W2 exclude any earlier common
point with first parameter greater than `a`. Injectivity excludes an earlier common point with first parameter
equal to `a`. […] Opposite original seeds are excluded by W0a, and a common seed cannot be revisited by a simple
path"), from: the W1 configuration does not occur (W2), no common open subarc on ordered prefixes (W0b), and the
second path does not visit the first seed (W0a for distinct seeds, or a common seed). -/
theorem noBackwardContact_of_not_isW1Configuration (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hW2 : ¬ IsW1Configuration α ζ₁ β ζ₂)
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c →
      ¬ HasCommonOpenSubarc α a β c)
    (hseed : 0 < ζ₁ → 0 < ζ₂ → α 0 = β 0 ∨ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → β t ≠ α 0) :
    NoBackwardContact α ζ₁ β ζ₂ := by
  intro A a t b₀ v₀ hA ht ht0 hE haA hp hab hb₀ hv₀ hq
  have hζ₁ : 0 < ζ₁ := lt_of_le_of_lt zero_le
    ((ENNReal.coe_lt_coe.2 (lt_of_le_of_lt zero_le (hab.trans_le hb₀))).trans hA)
  have hζ₂ : 0 < ζ₂ := lt_of_le_of_lt zero_le ((ENNReal.coe_lt_coe.2 ht0).trans ht)
  have hβt : β t ≠ β 0 := fun h =>
    (ne_of_gt ht0) (hβi ht.le (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₂ by rw [ENNReal.coe_zero]; exact zero_le) h)
  have hs1 : α a ≠ α 0 := by
    rw [hp]
    rcases hseed hζ₁ hζ₂ with h | h
    · rw [h]
      exact hβt
    · exact h t ht.le
  have ha0 : 0 < a := pos_iff_ne_zero.2 fun h => hs1 (by rw [h])
  exact hW2 ⟨A, t, a, b₀, v₀, hA.le, ht.le, hE, hp, hq, ha0, hab, hb₀, hv₀,
    fun v hv => hW0b A v hA ((ENNReal.coe_lt_coe.2 hv).trans ht) (hE v hv), hs1, by rw [hp]; exact hβt⟩

/-- **Theorem W5, pathwise, from the inputs of its proof**: on a sample where both curves are continuous and
injective on their available intervals, start at their seeds `x₂ ≤ x₁`, and satisfy W0a, W0b, W2, W4, the local
comparison at a common seed and the local frames, every pair of finite prefixes strictly before the lifetimes has
ordered proper completions. -/
theorem forall_hasOrderedProperCompletions_of_inputs {x₁ x₂ : ℝ} (hx : x₂ ≤ x₁)
    (hαc : ContinuousOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hβc : ContinuousOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ ζ₁}) (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hα0 : α 0 = x₁) (hβ0 : β 0 = x₂)
    (hW0a : x₂ < x₁ → 0 < ζ₁ → 0 < ζ₂ →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → β t ≠ x₁) ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → α s ≠ x₂))
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c →
      ¬ HasCommonOpenSubarc α a β c)
    (hW2 : ¬ IsW1Configuration α ζ₁ β ζ₂) (hW4 : ExtendsWithoutNewContact α ζ₁ β ζ₂)
    (hcs : x₂ = x₁ → 0 < ζ₁ → 0 < ζ₂ → ∃ a₀ c₀ : ℝ≥0, 0 < a₀ ∧ (a₀ : ℝ≥0∞) < ζ₁ ∧ 0 < c₀ ∧
      (c₀ : ℝ≥0∞) < ζ₂ ∧ HasOrderedProperCompletions α a₀ β c₀)
    (hloc : LocalCompletionAtContact α ζ₁ β ζ₂) :
    ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c := by
  refine forall_hasOrderedProperCompletions_of_firstLoss hαc hβc hαi (fun A hA0 hA hζ₂ => ?_) hW4
    (noBackwardContact_of_not_isW1Configuration hβi hW2 hW0b fun h1 h2 => ?_) hloc
  · rcases hx.lt_or_eq with hlt | heq
    · exact initial_of_distinctSeeds hαc hβc hW4 hlt hα0 hβ0
        (hW0a hlt (lt_of_le_of_lt zero_le hA) hζ₂).2 hA hζ₂
    · exact initial_of_commonSeed hαc hβc hαi hW4 (by rw [hα0, hβ0, heq]) (hcs heq) hA0 hA hζ₂
  · rcases hx.lt_or_eq with hlt | heq
    · exact Or.inr fun t ht => by rw [hα0]; exact (hW0a hlt h1 h2).1 t ht
    · exact Or.inl (by rw [hα0, hβ0, heq])

end Derived

/-! ### The almost-sure statements of §9 used by Theorem W5

Each is a statement of §9 on the frozen carriers, in the W5 setting (`0 < κ < 4`, piecewise-constant boundary data,
seeds `x₂ ≤ x₁`, angles `θ₁ < θ₂`, flow lines `η₁` from `x₁` at angle `θ₁` and `η₂` from `x₂` at angle `θ₂` of one
field), with the available lifetimes `ζᵢ` and only the prefixes strictly before them (the only ones W5 uses). Each
is therefore implied by its source statement. **None of them is proved in Lean**: their proofs use the conditioned
marked-kernel comparisons of supplement §7 (G3, G7, G7a, G8, G9, G2a), Lemma 7.7, the completion theorems G13, G13a
and the conformal joint-chart facts (Aux. lemmas 57, 83, 85, 90), which are not in Lean (handoff, "What remains"). -/

section Statements

/-- **Named input: Corollary W0a** (opposite original seeds are not visited, p. 528): "Let `x_β < x_α` and
`θ₁ < θ₂`, and assume that both original flows have nonzero available lifetime. Then neither flow visits the other
original seed, including at a finite terminal endpoint." Its weight computation is `w0a_right_weight`,
`w0a_left_weight`; the no-visit conclusion is Lemma G12's (§7, not in Lean). -/
def W0aStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, 0 < ζ₁ ω → 0 < ζ₂ ω →
        (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁) ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω s ≠ x₂)

/-- **Named input: Lemma W0b** (no common open arc on an ordered earlier prefix, p. 529): "For `θ₁ ≠ θ₂`, almost
surely no pair of original finite prefixes which admits the ordered proper completions of W0 contains a common
nontrivial open subarc." -/
def W0bStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c → ¬ HasCommonOpenSubarc (η₁ ω) a (η₂ ω) c

/-- **Named input: Lemma W2** (a backwards first loss is excluded by first-contact restart, p. 530): "For two
canonical constant-angle flows with `θ₁ < θ₂`, the event described in W1 has probability zero". The event of W1 is
`IsW1Configuration`. -/
def W2Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ¬ IsW1Configuration (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)

/-- **Named input: Lemma W4** (extension without a new mutual contact, p. 532), a deterministic statement about
"original simple Loewner prefixes", for the two flow lines on their almost-sure event of simplicity: their
available prefixes satisfy `ExtendsWithoutNewContact`. -/
def W4Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ExtendsWithoutNewContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)

/-- **Named input: Theorem W5's proof, the local comparison at a common seed** (p. 534): "For a common seed, use the
joint local comparison in Aux. lemma 97 with the two-height field matching the two original seed heights.
Proposition 7.4 supplies complete proper ordered reference paths. One common Cameron–Martin density and the
determining graphs, as in G1, transfer the entire pair stopped in a small seed neighborhood. Hence the two original
stopped prefixes have actual ordered proper completions." -/
def W5CommonSeedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, 0 < ζ₁ ω → 0 < ζ₂ ω → ∃ a₀ c₀ : ℝ≥0, 0 < a₀ ∧ (a₀ : ℝ≥0∞) < ζ₁ ω ∧ 0 < c₀ ∧
        (c₀ : ℝ≥0∞) < ζ₂ ω ∧ HasOrderedProperCompletions (η₁ ω) a₀ (η₂ ω) c₀

/-- **Named input: Theorem W5's proof, the local frames** (pp. 534–536, "Incoming active rational cuts", "The
interior and real local frames", "Splicing the rest of the current histories": "The comparison just proved gives
`𝓔(α([0, a₊]), β([0, b₊]))`"): almost surely `LocalCompletionAtContact`. The deterministic cut selection of these
paragraphs is `exists_incomingCuts`; the comparisons (G3, G9–G10, G8, G7a, G2a, G12, GB7a) are not in Lean. -/
def W5LocalFrameStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, LocalCompletionAtContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)

end Statements

/-! ### Theorem W5 -/

/-- A flow line starts at its seed almost surely (`η − x` is a generating trace, which starts at `0`). -/
theorem ae_apply_zero_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) : ∀ᵐ ω ∂P, η ω 0 = x := by
  obtain ⟨_, _, W, _, _, _, -, -, htr⟩ := hη
  filter_upwards [htr] with ω hω
  exact sub_eq_zero.1 hω.1

/-- **Theorem W5** (propagation of strict-prefix ordered completion, pp. 533–536), the frozen-carrier statement
`Theorem15.W5Statement` used by Theorem 1.5, from Aux. lemma 25 (simplicity, §4.2) and the six §9 statements
above. A conditional helper: W0a, W0b, W2, W4 and the two local comparisons of W5's proof are not proved in Lean.
Everything else in W5's proof (the initial order from W0a/W4 or the seed comparison/W4a, the first-loss parameter,
the exclusion of backwards contacts from W1–W2, the splice by W4a) is proved here. -/
theorem w5Statement_of_inputs (h25 : Theorem15.Aux25Statement.{u}) (hW0a : W0aStatement.{u})
    (hW0b : W0bStatement.{u}) (hW2 : W2Statement.{u}) (hW4 : W4Statement.{u})
    (hCS : W5CommonSeedStatement.{u}) (hLF : W5LocalFrameStatement.{u}) :
    Theorem15.W5Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hW0a' : ∀ᵐ ω ∂P, x₂ < x₁ → 0 < ζ₁ ω → 0 < ζ₂ ω →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁) ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω s ≠ x₂) := by
    by_cases hlt : x₂ < x₁
    · filter_upwards [hW0a κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hlt hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
        with ω hω _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hlt
  have hCS' : ∀ᵐ ω ∂P, x₂ = x₁ → 0 < ζ₁ ω → 0 < ζ₂ ω → ∃ a₀ c₀ : ℝ≥0, 0 < a₀ ∧
      (a₀ : ℝ≥0∞) < ζ₁ ω ∧ 0 < c₀ ∧ (c₀ : ℝ≥0∞) < ζ₂ ω ∧
        HasOrderedProperCompletions (η₁ ω) a₀ (η₂ ω) c₀ := by
    by_cases heq : x₂ = x₁
    · subst heq
      filter_upwards [hCS κ hκ hκ4 b jumps hb x₂ θ₁ θ₂ hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
        with ω hω _ using hω
    · exact Eventually.of_forall fun _ h => absurd h heq
  filter_upwards [Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₁, Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₂,
    ae_apply_zero_of_isFlowLine hη₁, ae_apply_zero_of_isFlowLine hη₂, hW0a', hCS',
    hW0b κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hW2 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hW4 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hLF κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
    with ω hc₁ hc₂ hi₁ hi₂ h0₁ h0₂ ha hcs hb0 hw2 hw4 hlf
  exact forall_hasOrderedProperCompletions_of_inputs hx hc₁ hc₂ hi₁ hi₂ h0₁ h0₂ ha hb0 hw2 hw4 hcs hlf

/-! ### Endpoint scope of W5: the closed stopped-order relation at finite thresholds -/

section Endpoint

/-- **The closed stopped-order relation** at finite thresholds `T₁`, `T₂` (§9, "Strict lifetime and terminal
conventions", p. 533: "At a genuine finite threshold, the closed stopped-order relation may be defined as the
closure of the strict-prefix ordered relation in the uniform spherical topology"): the two stopped curves, linearly
reparametrized on `[0, 1]`, are uniform limits of strict prefixes `α([0, a])`, `β([0, c])` (`a < T₁`, `c < T₂`) with
ordered proper completions. The Euclidean uniform distance is used; it dominates the spherical one, so this is the
stronger form. It is not an assertion that `𝓔` itself holds at the thresholds. -/
def IsClosedStoppedOrdered (α : ℝ≥0 → ℂ) (T₁ : ℝ≥0) (β : ℝ≥0 → ℂ) (T₂ : ℝ≥0) : Prop :=
  ∀ ε > 0, ∃ a c : ℝ≥0, a < T₁ ∧ c < T₂ ∧ HasOrderedProperCompletions α a β c ∧
    (∀ x ∈ Icc (0 : ℝ≥0) 1, dist (α (x * T₁)) (α (x * a)) < ε) ∧
    ∀ x ∈ Icc (0 : ℝ≥0) 1, dist (β (x * T₂)) (β (x * c)) < ε

/-- Linear reparametrizations of late prefixes converge uniformly ("Endpoint continuity", p. 533). -/
theorem exists_lt_forall_dist_lt {γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) (hγ : ContinuousOn γ (Icc 0 T))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ l < T, ∀ a : ℝ≥0, l < a → a ≤ T → ∀ x ∈ Icc (0 : ℝ≥0) 1, dist (γ (x * T)) (γ (x * a)) < ε := by
  obtain ⟨δ, hδ, hu⟩ :=
    Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hγ) ε hε
  refine ⟨T - δ.toNNReal, tsub_lt_self hT (Real.toNNReal_pos.2 hδ), fun a hla haT x hx => ?_⟩
  have hx1 : x * T ≤ T := mul_le_of_le_one_left zero_le hx.2
  refine hu _ ⟨zero_le, hx1⟩ _ ⟨zero_le, (mul_le_of_le_one_left zero_le hx.2).trans haT⟩ ?_
  have hla' := NNReal.coe_lt_coe.2 hla
  rw [NNReal.coe_sub_def, Real.coe_toNNReal _ hδ.le] at hla'
  have hTa : (T : ℝ) - δ < a := (le_max_left _ _).trans_lt hla'
  have hx0 : (0 : ℝ) ≤ x := x.2
  have hx1' : (x : ℝ) ≤ 1 := NNReal.coe_le_coe.2 hx.2
  have haT' : (a : ℝ) ≤ T := NNReal.coe_le_coe.2 haT
  rw [NNReal.dist_eq, NNReal.coe_mul, NNReal.coe_mul, abs_sub_lt_iff]
  constructor <;> nlinarith

/-- **Endpoint scope of W5** (p. 536: "The closed stopped-order relation defined above follows at finite thresholds
by continuous limits"), deterministically: if every strict pair has ordered proper completions and the curves are
continuous up to the positive finite thresholds, the stopped pair is in the closed stopped-order relation. -/
theorem isClosedStoppedOrdered_of_forall_lt {α β : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0} (h1 : 0 < T₁) (h2 : 0 < T₂)
    (hα : ContinuousOn α (Icc 0 T₁)) (hβ : ContinuousOn β (Icc 0 T₂))
    (hE : ∀ a c : ℝ≥0, a < T₁ → c < T₂ → HasOrderedProperCompletions α a β c) :
    IsClosedStoppedOrdered α T₁ β T₂ := by
  intro ε hε
  obtain ⟨l₁, hl₁, h₁⟩ := exists_lt_forall_dist_lt h1 hα hε
  obtain ⟨l₂, hl₂, h₂⟩ := exists_lt_forall_dist_lt h2 hβ hε
  obtain ⟨a, ha1, ha2⟩ := exists_between hl₁
  obtain ⟨c, hc1, hc2⟩ := exists_between hl₂
  exact ⟨a, c, ha2, hc2, hE a c ha2 hc2, h₁ a ha1 ha2.le, h₂ c hc1 hc2.le⟩

/-- **Theorem W5 at finite thresholds** (pp. 528, 533, 536): from `Theorem15.W5Statement`, almost surely, when both
available lifetimes are finite and positive, the full stopped pair is in the closed stopped-order relation. -/
theorem ae_isClosedStoppedOrdered_of_w5 (hW5 : Theorem15.W5Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ}
    (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ T₁ T₂ : ℝ≥0, ζ₁ ω = T₁ → ζ₂ ω = T₂ → 0 < T₁ → 0 < T₂ →
      IsClosedStoppedOrdered (η₁ ω) T₁ (η₂ ω) T₂ := by
  filter_upwards [hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂]
    with ω hω hc₁ hc₂ T₁ T₂ hT₁ hT₂ h1 h2
  rw [hT₁] at hω hc₁
  rw [hT₂] at hω hc₂
  refine isClosedStoppedOrdered_of_forall_lt h1 h2 ?_ ?_ fun a c ha hc =>
    hω a c (ENNReal.coe_lt_coe.2 ha) (ENNReal.coe_lt_coe.2 hc)
  · rw [← setOf_coe_le_coe_eq_Icc]
    exact hc₁
  · rw [← setOf_coe_le_coe_eq_Icc]
    exact hc₂

end Endpoint

/-! ### Corollary W0a from Lemma G12 -/

section W0aFromG12

/-- The seed group of a flow-line force word: the only mark at the seed is the first one. -/
theorem sum_filter_cons_eq_zero {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j, f j ≠ 0) (ρ₀ : ℝ) (ρ : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (Fin.cons (0 : ℝ) f : Fin (n + 1) → ℝ) i = 0),
      (Fin.cons ρ₀ ρ : Fin (n + 1) → ℝ) i = ρ₀ := by
  have : Finset.univ.filter (fun i : Fin (n + 1) => (Fin.cons (0 : ℝ) f : Fin (n + 1) → ℝ) i = 0) =
      {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hf j, Fin.succ_ne_zero]
  rw [this, Finset.sum_singleton, Fin.cons_zero]

/-- **Positive lifetime requires admissible seed groups** (W0a's proof, p. 528: "positive initial lifetime requires
both seed groups to exceed `−2`"): almost surely, if `ζ > 0` the left and right seed weights of the flow-line word
exceed `−2` (the frozen lifetime has no threshold at time `0 < ζ`, `IsIntegratedSLEPath`). -/
theorem ae_seedWeights_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, 0 < ζ ω →
      -2 < Sec4.cumWeightLeft κ (PiecewiseConstantBoundaryData.leftLim b x + θ * QuantumZipper.chiC κ) ∧
      -2 < Sec4.cumWeightRight κ (PiecewiseConstantBoundaryData.rightLim b x + θ * QuantumZipper.chiC κ) := by
  obtain ⟨_, _, W, VL, VR, B, -, hcoup, -⟩ := hη
  filter_upwards [hcoup.1.2.2.2.2] with ω hp hζ
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -⟩ := hp
  have h0 := hnt 0 (by rwa [ENNReal.coe_zero])
  simp only [ForceWord.ThresholdCondition, not_or, not_le, hw0, hvL0, hvR0] at h0
  set SL := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter (· < x)
  set SR := (PiecewiseConstantBoundaryData.jumpSet b jumps).filter (x < ·)
  have kL := sum_filter_cons_eq_zero (fun i => SL.orderEmbOfFin rfl (Fin.rev i) - x)
    (fun j => (sub_neg.2 (Finset.mem_filter.1 (SL.orderEmbOfFin_mem rfl _)).2).ne)
    (-(PiecewiseConstantBoundaryData.leftLim b x + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
    (fun i => let y := SL.orderEmbOfFin rfl (Fin.rev i)
      (PiecewiseConstantBoundaryData.rightLim b y - PiecewiseConstantBoundaryData.leftLim b y) / sleLambda κ)
  have kR := sum_filter_cons_eq_zero (fun i => SR.orderEmbOfFin rfl i - x)
    (fun j => (sub_pos.2 (Finset.mem_filter.1 (SR.orderEmbOfFin_mem rfl _)).2).ne')
    ((PiecewiseConstantBoundaryData.rightLim b x + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
    (fun i => let y := SR.orderEmbOfFin rfl i
      (PiecewiseConstantBoundaryData.rightLim b y - PiecewiseConstantBoundaryData.leftLim b y) / sleLambda κ)
  exact ⟨lt_of_lt_of_eq h0.1 kL, lt_of_lt_of_eq h0.2 kR⟩

/-- **Named input: Lemma G12 for a flow line** (nonseed marked points above their cumulative threshold are polar;
supplement §7, p. 504), in the form in which W0a applies it (p. 528: "Apply G12, reflecting in the second case. If a
seed is not already a boundary jump for the other flow, retain it as a passive zero-weight mark; this does not
change the driving law or the displayed cumulative weight"): for the angle-`θ` flow line from `x`, a real point
`y > x` whose outward right cumulative weight `S = (b(y⁺) + θχ)/λ − 1` exceeds `d_* = κ/2 − 4` is almost surely not
visited, including at a finite terminal endpoint; reflected for `y < x`, with `S = −(b(y⁻) + θχ)/λ − 1`. (For
piecewise-constant `b` the partial sum `Σ_{k ≤ j} ρ_{k,R}` of the flow-line weights up to the mark `y` telescopes to
this `S`.) A §7 statement, **not proved in Lean**. -/
def G12FlowStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ y : ℝ,
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ →
      (x < y → κ / 2 - 4 <
          Sec4.cumWeightRight κ (PiecewiseConstantBoundaryData.rightLim b y + θ * QuantumZipper.chiC κ) →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
      (y < x → κ / 2 - 4 <
          Sec4.cumWeightLeft κ (PiecewiseConstantBoundaryData.leftLim b y + θ * QuantumZipper.chiC κ) →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y)

/-- **Corollary W0a** (p. 528) from Lemma G12: the weight computation `w0a_right_weight`, `w0a_left_weight` and the
seed admissibility of a positive lifetime (`ae_seedWeights_of_isFlowLine`). If the displayed cumulative weight at
the other seed is at most `d_κ`, the own seed group is at most `−2`, and then the own lifetime vanishes almost
surely. -/
theorem w0aStatement_of_g12 (hG12 : G12FlowStatement.{u}) : W0aStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have e₂ : ∀ᵐ ω ∂P, 0 < ζ₁ ω → ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁ := by
    by_cases hS : κ / 2 - 4 <
        Sec4.cumWeightRight κ (PiecewiseConstantBoundaryData.rightLim b x₁ + θ₂ * QuantumZipper.chiC κ)
    · filter_upwards [(hG12 κ hκ hκ4 b jumps hb x₂ θ₂ x₁ P h hh η₂ ζ₂ hη₂).1 hx hS] with ω hω _ using hω
    · filter_upwards [ae_seedWeights_of_isFlowLine hη₁] with ω hω hζ
      have hw := w0a_right_weight hκ hκ4 hθ (hω hζ).2
      exact absurd (hw.2.2.trans hw.2.1) hS
  have e₁ : ∀ᵐ ω ∂P, 0 < ζ₂ ω → ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω s ≠ x₂ := by
    by_cases hS : κ / 2 - 4 <
        Sec4.cumWeightLeft κ (PiecewiseConstantBoundaryData.leftLim b x₂ + θ₁ * QuantumZipper.chiC κ)
    · filter_upwards [(hG12 κ hκ hκ4 b jumps hb x₁ θ₁ x₂ P h hh η₁ ζ₁ hη₁).2 hx hS] with ω hω _ using hω
    · filter_upwards [ae_seedWeights_of_isFlowLine hη₂] with ω hω hζ
      have hw := w0a_left_weight hκ hκ4 hθ (hω hζ).1
      exact absurd (hw.2.2.trans hw.2.1) hS
  filter_upwards [e₂, e₁] with ω h2 h1 hζ₁ hζ₂ using ⟨h2 hζ₁, h1 hζ₂⟩

end W0aFromG12

end Supp9

end InteractingSLE
