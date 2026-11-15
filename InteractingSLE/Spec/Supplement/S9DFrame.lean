/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9DW2

/-!
# Supplement §9: W5's local frames, reduced to the local comparison at dyadic retained pairs

Packet PROVE-W5-REST. Source: Theorem W5's proof (`source/spec/p529-576.md` L140–L180, pp. 534–536), paragraphs
"Incoming active rational cuts", "The interior and real local frames" and "Splicing the rest of the current
histories".

W5's proof at the first loss `p = α(a) = β(τ)`: "The earlier contact relation is increasing. On every earlier
completed prefix W0b excludes a common open subarc […] Choose rational interior parameters in one such gap. If
earlier contacts do not accumulate at `p`, choose rational cuts in the two final contact-free incoming arcs instead.
Write these cuts as `r < a` and `s < τ`. Their second parameter is strictly before the first loss, so their old
prefixes have ordered proper completions. The fresh incoming arcs from them to `p` avoid both old prefixes […] The
opposite-hull exclusion in W1 therefore applies to both tips […] Aux. lemma 90 gives joint activity […] The current
tips are interior and distinct." Then the local comparison (G3 for interior `p`; G8 or G2a with G7a for real `p`) and
G9–G10 with the planar gluing give `𝓔(α([0, a₊]), β([0, b₊]))`: "This is a countable stopped-law comparison".

This file proves the selection of the dyadic incoming cuts and the verification of the ordinary retained pair, and
derives `Supp9.W5LocalFrameStatement` from W0b, W0a, Aux. 25 and the named local comparison at dyadic ordinary
retained pairs, `RetainedLocalCompletionStatement`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp9D

open Sec2.Assembly Supp9 Sec7

/-! ### Incoming cuts off both earlier prefixes -/

section Incoming

variable {α β : ℝ≥0 → ℂ}

/-- **The incoming cuts of W5's proof** (pp. 534–535), `Supp9.exists_incomingCuts` with two more conclusions: the
first tip `α(r)` is off the whole second prefix `β([0, τ])` and the second tip `β(s)` is off the whole first prefix
`α([0, a])` (both cuts lie in a matched contact-free gap). The proof is that of `Supp9.exists_incomingCuts`. -/
theorem exists_incomingCuts' {a τ : ℝ≥0} (hα : ContinuousOn α (Icc 0 a)) (hβ : ContinuousOn β (Icc 0 τ))
    (hαi : InjOn α (Icc 0 a)) (hβi : InjOn β (Icc 0 τ)) (hinc : EarlierContactsIncreasing α a β τ)
    (hp : α a = β τ) (ha0 : 0 < a) (hτ0 : 0 < τ) (harc : ∀ v < τ, ¬ HasCommonOpenSubarc α a β v)
    {R S : Set ℝ≥0} (hR : Dense R) (hS : Dense S) {δ : ℝ≥0} (hδ : 0 < δ) :
    ∃ r s : ℝ≥0, r ∈ R ∧ s ∈ S ∧ a - δ < r ∧ r < a ∧ τ - δ < s ∧ s < τ ∧ α r ≠ β s ∧
      Disjoint (α '' Ioc r a) (β '' Icc 0 s) ∧ Disjoint (β '' Ioc s τ) (α '' Icc 0 r) ∧
      (∀ y ≤ τ, α r ≠ β y) ∧ (∀ x ≤ a, α x ≠ β s) := by
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
      ?_, ?_, ?_, ?_, ?_⟩
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
    · intro y hy hxy
      have hq := hmem r y hra.le hy hxy
      rcases le_or_gt r x with h | h
      · exact absurd (hlow _ hq h).1 (not_le.2 hr1)
      · exact absurd (hhi _ hq h.le) (not_le.2 hr2)
    · intro x' hx' hxy
      have hq := hmem x' s hx' hsτ.le hxy
      rcases le_or_gt x' x with h | h
      · exact absurd (hlow _ hq h).2 (not_le.2 hs1)
      · exact absurd (hge _ hq h) (not_le.2 hs2)
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

end Incoming

/-! ### The local comparison at a dyadic retained pair -/

/-- **Named input: the local comparison of W5's proof at a retained pair** (Theorem W5's proof, pp. 535–536, "The
interior and real local frames" and the first sentence of "Splicing the rest of the current histories"; Lemmas G3,
G7a, G8, G2a, G9, G10 and the planar gluing of the stopped reference tangle, supplement §7, pp. 492–503). Setting of
`Supp9.W5LocalFrameStatement`. For all own cutoffs `(u, r)`, almost surely: if `(u, r)` is an ordinary retained pair
(`Supp7.IsOrdinaryRetainedPair`: interior tips, each off the other prefix, jointly active, ordered completions) and
the fresh portions `η₁((u, a])`, `η₂((r, τ])`, strictly before the lifetimes, avoid the retained union
`A = η₁([0, u]) ∪ η₂([0, r])` and end at a common point `η₁(a) = η₂(τ)`, then for some `a₂ > a` and `b₂ > τ` within the
lifetimes the enlarged prefixes have ordered proper completions.

In the source: at the retained pair, G3 (interior contact point) or G8 / G2a with G7a (real contact point) compares
the stopped fresh pair law, in a buffer containing the fresh arcs and short outgoing portions, with a complete
ordered reference under one positive density; G9 puts the reference tails in the joint chart with the higher-angle
path on the left, G10 interiorizes, and the planar gluing appends them to the old ordered completions ("The comparison
just proved gives `𝓔(α([0, a₊]), β([0, b₊]))`"). The conclusion is also implied by Theorem W5 itself
(`Theorem15.W5Statement`), so this input is true; it is the countable stopped-law comparison only, without the
first-loss induction, the selection of the cuts, W0b or the activity argument. **Not proved in Lean.** -/
def RetainedLocalCompletionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0, ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
      ∀ a τ : ℝ≥0, u < a → (a : ℝ≥0∞) < ζ₁ ω → r < τ → (τ : ℝ≥0∞) < ζ₂ ω → η₁ ω a = η₂ ω τ →
        (∀ x : ℝ≥0, u < x → x ≤ a → η₁ ω x ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        (∀ y : ℝ≥0, r < y → y ≤ τ → η₂ ω y ∉ η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ω ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ω ∧
          HasOrderedProperCompletions (η₁ ω) a₂ (η₂ ω) b₂

/-! ### The local frames -/

/-- The dyadic times at which a path is interior, together with all times after the lifetime, are dense. -/
theorem dense_goodCuts {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hc : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ ζ})
    (hno : ∀ x y : ℝ≥0, x < y → (y : ℝ≥0∞) < ζ → ∃ z ∈ Ioo x y, γ z ∈ QuantumZipper.H) :
    Dense ({r | r ∈ dyadSet ∧ γ r ∈ QuantumZipper.H} ∪ {r : ℝ≥0 | ζ ≤ r}) := by
  refine dense_of_exists_between fun x y hxy => ?_
  by_cases hy : (y : ℝ≥0∞) ≤ ζ
  · obtain ⟨y', hxy', hy'y⟩ := exists_between hxy
    obtain ⟨r, hr, hxr, hry', hrH⟩ := exists_dyad_mem_H hc hno hxy'
      (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hy'y) hy)
    exact ⟨r, Or.inl ⟨hr, hrH⟩, hxr, hry'.trans hy'y⟩
  · have hζ : ζ < (y : ℝ≥0∞) := not_le.1 hy
    obtain ⟨z, hz1, hz2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hζ
    obtain ⟨w, hw1, hw2⟩ := exists_between (max_lt hxy (ENNReal.coe_lt_coe.1 hz2))
    exact ⟨w, Or.inr (hz1.le.trans (ENNReal.coe_le_coe.2 ((le_max_right _ _).trans hw1.le))),
      (le_max_left _ _).trans_lt hw1, hw2⟩

/-- **W5's local frames, pathwise** (pp. 534–536), from W0b on the prefixes, the pathwise facts, and the local
comparison at every dyadic ordinary retained pair. -/
theorem localCompletionAtContact_of_retained {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} (hF : PathFacts α ζ₁ β ζ₂)
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c →
      ¬ HasCommonOpenSubarc α a β c)
    (hloc : ∀ u ∈ dyadSet, ∀ r ∈ dyadSet, Supp7.IsOrdinaryRetainedPair α ζ₁ u β ζ₂ r →
      ∀ a τ : ℝ≥0, u < a → (a : ℝ≥0∞) < ζ₁ → r < τ → (τ : ℝ≥0∞) < ζ₂ → α a = β τ →
        (∀ x : ℝ≥0, u < x → x ≤ a → α x ∉ α '' Icc 0 u ∪ β '' Icc 0 r) →
        (∀ y : ℝ≥0, r < y → y ≤ τ → β y ∉ α '' Icc 0 u ∪ β '' Icc 0 r) →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ∧
          HasOrderedProperCompletions α a₂ β b₂) :
    LocalCompletionAtContact α ζ₁ β ζ₂ := by
  intro a τ ha hτ hτ0 hp hE
  have hle₁ : ∀ x : ℝ≥0, x ≤ a → (x : ℝ≥0∞) ≤ ζ₁ := fun x hx => (ENNReal.coe_le_coe.2 hx).trans ha.le
  have hle₂ : ∀ y : ℝ≥0, y ≤ τ → (y : ℝ≥0∞) ≤ ζ₂ := fun y hy => (ENNReal.coe_le_coe.2 hy).trans hτ.le
  have h₁ : 0 < ζ₁ := lt_of_le_of_lt zero_le ha
  have h₂ : 0 < ζ₂ := lt_of_le_of_lt zero_le hτ
  have ha0 : 0 < a := by
    refine pos_iff_ne_zero.2 fun ha0 => ?_
    have := hF.eq_zero_of_eq_α0 h₁ h₂ (hle₂ τ le_rfl) (by rw [← hp, ha0])
    exact absurd this hτ0.ne'
  have hinc := Supp9.earlierContactsIncreasing_of_contactOrder Supp9B.orderedContactOrderStatement hF.α0 hF.β0
    hF.seed hE
  have harc : ∀ v < τ, ¬ HasCommonOpenSubarc α a β v := fun v hv =>
    hW0b a v ha (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hv) (hle₂ τ le_rfl)) (hE v hv)
  obtain ⟨r, s, hrR, hsS, -, hra, -, hsτ, -, hd1, hd2, hrβ, hsα⟩ :=
    exists_incomingCuts' (hF.αc.mono fun x hx => hle₁ x hx.2) (hF.βc.mono fun y hy => hle₂ y hy.2)
      (hF.αi.mono fun x hx => hle₁ x hx.2) (hF.βi.mono fun y hy => hle₂ y hy.2) hinc hp ha0 hτ0 harc
      (dense_goodCuts hF.αc hF.αno) (dense_goodCuts hF.βc hF.βno) ha0
  have hrζ : (r : ℝ≥0∞) < ζ₁ := lt_trans (ENNReal.coe_lt_coe.2 hra) ha
  have hsζ : (s : ℝ≥0∞) < ζ₂ := lt_trans (ENNReal.coe_lt_coe.2 hsτ) hτ
  obtain ⟨hrD, hrH⟩ : r ∈ dyadSet ∧ α r ∈ QuantumZipper.H := hrR.resolve_right fun h => absurd h (not_le.2 hrζ)
  obtain ⟨hsD, hsH⟩ : s ∈ dyadSet ∧ β s ∈ QuantumZipper.H := hsS.resolve_right fun h => absurd h (not_le.2 hsζ)
  have hαfresh : ∀ x ∈ Icc r a, α x ∉ β '' Icc 0 s := by
    rintro x hx ⟨y, hy, hyx⟩
    rcases hx.1.lt_or_eq with hrx | hrx
    · exact Set.disjoint_left.1 hd1 ⟨x, ⟨hrx, hx.2⟩, rfl⟩ ⟨y, hy, hyx⟩
    · exact hrβ y (hy.2.trans hsτ.le) (hrx ▸ hyx.symm)
  have hβfresh : ∀ y ∈ Icc s τ, β y ∉ α '' Icc 0 r := by
    rintro y hy ⟨x, hx, hxy⟩
    rcases hy.1.lt_or_eq with hsy | hsy
    · exact Set.disjoint_left.1 hd2 ⟨y, ⟨hsy, hy.2⟩, rfl⟩ ⟨x, hx, hxy⟩
    · exact hsα x (hx.2.trans hra.le) (hsy ▸ hxy)
  have hord : Supp7.IsOrdinaryRetainedPair α ζ₁ r β ζ₂ s :=
    isOrdinaryRetainedPair_of_cuts hF.α0 hF.β0 hF.seed
      (Supp9.HasOrderedProperCompletions.mono (hE s hsτ) hra.le le_rfl)
      (hF.αc.mono fun x hx => hle₁ x hx.2) (hF.βc.mono fun y hy => hle₂ y hy.2)
      (fun x _ hxa => completion_left_of_le (hE 0 hτ0) hxa.le)
      (fun y _ hyτ => completion_right_of_le (hE y hyτ) le_rfl)
      (fun x hx => hF.αim x (hle₁ x hx)) (fun y hy => hF.βim y (hle₂ y hy)) hra le_rfl hsτ le_rfl hp hp
      hrH hsH hαfresh hβfresh hrζ hsζ
  refine hloc r hrD s hsD hord a τ hra ha hsτ hτ hp ?_ ?_
  · rintro x hrx hxa (⟨x', hx', hxx'⟩ | hxβ)
    · have := hF.αi (hle₁ x' (hx'.2.trans hra.le)) (hle₁ x hxa) hxx'
      exact absurd (this ▸ hx'.2) (not_le.2 hrx)
    · exact hαfresh x ⟨hrx.le, hxa⟩ hxβ
  · rintro y hsy hyτ (hyα | ⟨y', hy', hyy'⟩)
    · exact hβfresh y ⟨hsy.le, hyτ⟩ hyα
    · have := hF.βi (hle₂ y' (hy'.2.trans hsτ.le)) (hle₂ y hyτ) hyy'
      exact absurd (this ▸ hy'.2) (not_le.2 hsy)

/-- **W5's local frames** (`Supp9.W5LocalFrameStatement`) from Aux. lemma 25, W0a, W0b and the local comparison at
dyadic retained pairs. -/
theorem w5LocalFrameStatement_of_inputs (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (hL : RetainedLocalCompletionStatement.{u}) :
    Supp9.W5LocalFrameStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hLall : ∀ᵐ ω ∂P, ∀ p : (ℕ × ℕ) × (ℕ × ℕ),
      Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) (dyad p.1.1 p.1.2) (η₂ ω) (ζ₂ ω) (dyad p.2.1 p.2.2) →
      ∀ a τ : ℝ≥0, dyad p.1.1 p.1.2 < a → (a : ℝ≥0∞) < ζ₁ ω → dyad p.2.1 p.2.2 < τ → (τ : ℝ≥0∞) < ζ₂ ω →
        η₁ ω a = η₂ ω τ →
        (∀ x : ℝ≥0, dyad p.1.1 p.1.2 < x → x ≤ a →
          η₁ ω x ∉ η₁ ω '' Icc 0 (dyad p.1.1 p.1.2) ∪ η₂ ω '' Icc 0 (dyad p.2.1 p.2.2)) →
        (∀ y : ℝ≥0, dyad p.2.1 p.2.2 < y → y ≤ τ →
          η₂ ω y ∉ η₁ ω '' Icc 0 (dyad p.1.1 p.1.2) ∪ η₂ ω '' Icc 0 (dyad p.2.1 p.2.2)) →
        ∃ a₂ b₂ : ℝ≥0, a < a₂ ∧ (a₂ : ℝ≥0∞) < ζ₁ ω ∧ τ < b₂ ∧ (b₂ : ℝ≥0∞) < ζ₂ ω ∧
          HasOrderedProperCompletions (η₁ ω) a₂ (η₂ ω) b₂ :=
    ae_all_iff.2 fun p => hL κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
      (dyad p.1.1 p.1.2) (dyad p.2.1 p.2.2)
  filter_upwards [ae_pathFacts h25 hW0a hκ hκ4 hb hx hθ hh hη₁ hη₂,
    hW0b κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, hLall] with ω hF hb0 hl
  refine localCompletionAtContact_of_retained hF hb0 ?_
  rintro u ⟨⟨n, k⟩, rfl⟩ r ⟨⟨n', k'⟩, rfl⟩
  exact hl ((n, k), (n', k'))

/-- **Theorem W5** (`Theorem15.W5Statement`, the input of Theorem 1.5) from Aux. lemma 25, W0a, W0b, Lemma 7.7 (on the
canonical space), the joint G7 carrier, the local comparison at dyadic retained pairs, and the common-seed local
comparison. -/
theorem w5Statement_of_inputs'' (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hL : RetainedLocalCompletionStatement.{u}) (hCS : Supp9.W5CommonSeedStatement.{u}) :
    Theorem15.W5Statement.{u} :=
  w5Statement_of_inputs' h25 hW0a hW0b h77 hJ hCS (w5LocalFrameStatement_of_inputs h25 hW0a hW0b hL)

end Supp9D

end InteractingSLE
