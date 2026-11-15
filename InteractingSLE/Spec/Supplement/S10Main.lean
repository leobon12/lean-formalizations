/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S10Order
import InteractingSLE.Spec.Sec7.InteractionProbLemma77
import InteractingSLE.Spec.Sec7.InteractionMerge
import InteractingSLE.Frozen.Spec.activeDomain
import InteractingSLE.Frozen.Spec.IsActiveChart

/-!
# Supplement §10 for flow lines: W6, W8 and the Theorem 1.5 inputs from named inputs

Packet PROVE-SUPP10 (specification supplement §10, `source/spec/p529-576.md`, pp. 536–544). Statements on the
frozen carriers (`IsFlowLine`, `IsFirstContact`, `CrossesFromRightAt`, `AgreeAsCurvesAfter`, `activeDomain`), with
the available lifetimes `ζᵢ` of `IsFlowLine` as the source's own-filtration stops `Tᵢ` (as in
`Theorem15Inputs.lean`).

## Named inputs from other sections (not in Lean yet)

| Input | Source |
|---|---|
| `Lemma77Statement` | Lemma 7.7, §7.2, p. 282: common first point and confinement (`Tᵢ = ζᵢ`) |
| `W2aStatement` | Lemma W2a, supplement §9, p. 533, with linear clocks on `[0, A] × [0, B]` |
| `G5Statement` (`S10Order.lean`) | Lemma G5, supplement §7.5, p. 494 (deterministic) |
| `Theorem15.W5Statement` | Theorem W5, supplement §9, pp. 533–534 |
| `Theorem15.Aux25Statement` | Aux. lemma 25, §4.2, p. 127 |

## Proved here

* **Lemma W6** (p. 537) for two flow lines from one real seed with distinct angles (`w6Statement_of_inputs`): all
  finite-parameter contacts, finite thresholds included, are increasing.
* **Theorem W8, common-seed selection** (pp. 539–540; `w8CommonSeedStatement_of_w6`): for the canonical pair from
  one seed, for every start `σ` the later contact relation has a coordinatewise least element (one common point),
  and (W8.2) neither tail returns to the selected prefixes.
* **Theorem W8 at `σ = 0`**, the Theorem 1.5 input `Theorem15.W8FirstContactStatement`
  (`w8FirstContactStatement_of_lemma77`): "Suppose instead their finite global first contact is `w`. The established
  first-contact theorem supplies [it]" (p. 539).

## Conditional helpers (the remaining proposition is named)

The other §10 conclusions for the original flows are obtained in the source by applying W5, W6 and 7.12D *under the
regular conditional law* of the first-contact restart (Lemma 7.8, Theorem 7.9B), in the common active chart, and
pulling back through the chart. That conditional step has no Lean carrier yet (see the handoff). Each helper below
isolates it as one named proposition, and proves the rest of the source argument:

* `w8LaterSelectionStatement_of_contactsIncreasing`: W8's common later selection and no return for the original
  flows, from increasing contact order of the original flows (`OriginalContactsIncreasingStatement`, which is W6 for
  the conditional common-seed pair transported by W7);
* `criticalExclusionAfterCrossingStatement_of_inputs`: the Theorem 1.5 input
  `Theorem15.CriticalExclusionAfterCrossingStatement`, from Lemma 7.7, Aux. 25 and the exclusion of later common
  points inside the active domain (`ChartInteriorExclusionStatement`, 7.12D for the conditional pair pulled back by
  the chart). The §10 step proved here: "First-contact confinement and no return put every subsequent common point
  of the original open domain in the interior of this chart" (`mem_activeDomain_of_later`);
* `thm712CMergingStatement_of_inputs`: the Theorem 1.5 input `Theorem15.Thm712CMergingStatement`, from the common
  conditional flow after the first contact (`CommonFlowAfterFirstContactStatement`; "Universal finite-force
  determination gives one canonical path function. The two actual futures are that same path stopped at their
  respective reconstructed own stopping times", p. 542);
* `thm712CCrossingStatement_of_inputs`: the Theorem 1.5 input `Theorem15.Thm712CCrossingStatement`, from Lemma 7.7's
  confinement and the chart order of the conditional pair (`ChartOrderAfterCrossingStatement`, W5 for the conditional
  pair).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp10

open Sec7 Theorem15

/-! ### Basic facts about flow lines -/

/-- Almost surely a flow line from `x` starts at `x` (its translate is a generating trace, which starts at `0`). -/
theorem ae_apply_zero_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) : ∀ᵐ ω ∂P, η ω 0 = x := by
  obtain ⟨_, _, W, _, _, _, -, -, htr⟩ := hη
  filter_upwards [htr] with ω hω
  exact sub_eq_zero.mp hω.1

/-- Increasing contact order is symmetric (for an injective second curve). -/
theorem ContactsIncreasing.swap {α β : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0∞} (h : ContactsIncreasing α T₁ β T₂)
    (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂}) : ContactsIncreasing β T₂ α T₁ := by
  intro p hp q hq hlt
  have hp' : p.swap ∈ stoppedContactSet α 0 T₁ β 0 T₂ := swap_mem_stoppedContactSet.mp (by simpa using hp)
  have hq' : q.swap ∈ stoppedContactSet α 0 T₁ β 0 T₂ := swap_mem_stoppedContactSet.mp (by simpa using hq)
  exact h.fst_lt_of_snd_lt hβi hp' hq' hlt

/-! ### Named inputs -/

/-- **Named input: Lemma 7.7** (§7.2, p. 282), its common-first-point and confinement clauses with `Tᵢ = ζᵢ`:
"Fix `x₁, x₂ ∈ ∂ℍ` with `x₂ < x₁` and angles `θ₁, θ₂` with `θ₁ < θ₂ + π`. […] if `τᵢ ≤ Tᵢ` and `τᵢ < ∞` for
`i = 1, 2` then `η₁(τ₁) = η₂(τ₂)` and the range of `ηᵢ|[τᵢ, Tᵢ]`, for `i = 1, 2`, is almost surely contained in the
Euclidean closure of the unbounded connected component of `ℍ \ K`", `K = η₁([0, τ₁ ∧ T₁]) ∪ η₂([0, τ₂ ∧ T₂])`.
Attained first contacts at one common point are `IsFirstContact` (finite terminal values included, p. 283); the
unbounded component is the frozen `activeDomain`. (The local-set clause of Lemma 7.7 is not used here and omitted.)
-/
def Lemma77Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω ∧ (t : ℝ≥0∞) ≤ ζ₂ ω ∧ η₁ ω s = η₂ ω t) →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          (∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ ω →
            η₁ ω s ∈ closure (activeDomain (η₁ ω) s₀ (η₂ ω) t₀)) ∧
          ∀ t : ℝ≥0, t₀ ≤ t → (t : ℝ≥0∞) ≤ ζ₂ ω →
            η₂ ω t ∈ closure (activeDomain (η₁ ω) s₀ (η₂ ω) t₀)

/-- **Named input: Lemma W2a** (a reversed frontier pair is also excluded; supplement §9, p. 533), for the flow
lines of W5 (`x₂ ≤ x₁`, `θ₁ < θ₂`) and the linear clocks `A(u) = uA`, `B(u) = uB` on `u ∈ [0, 1]`: almost surely,
for every rectangle `[0, A] × [0, B]` inside the available ranges whose strict prefix pairs all have ordered proper
completions, "the new contacts on its top or right edge cannot reverse the increasing order of the contacts in its
strict interior, nor can the two new edge contacts be distinct and reverse one another" (`NoReversedFrontierPair`).
The hypothesis "every pair of prefixes at `u < τ` has ordered proper completions" is required here for all strict
pairs `a < A`, `c < B` (a stronger hypothesis, so this is implied by W2a). -/
def W2aStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ A B : ℝ≥0, (A : ℝ≥0∞) ≤ ζ₁ ω → (B : ℝ≥0∞) ≤ ζ₂ ω →
        (∀ a c : ℝ≥0, a < A → c < B → HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) →
        NoReversedFrontierPair (η₁ ω) A (η₂ ω) B

/-! ### Lemma W6 -/

/-- **Lemma W6** (contact order through finite terminal endpoints; supplement §10, p. 537): "Let two maximal
canonical finite-word flows from one real seed have distinct angles and admissible initial seed groups. Their finite
common points occur in increasing parameter order, including a common point at a finite continuation threshold of
either path." (An inadmissible seed gives lifetime `0`, R15 Q1; the statement then holds trivially.) -/
def W6Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ₁ θ₂ : ℝ, θ₁ ≠ θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)

/-- **Lemma W6, ordered angles**: the lower-angle path `η₁` and the higher-angle path `η₂` from one seed. -/
theorem w6_of_lt (hW5 : W5Statement.{u}) (hW2a : W2aStatement.{u}) (hG5 : G5Statement)
    (hA25 : Aux25Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} (h₁ : IsFlowLine κ b jumps x θ₁ P h η₁ ζ₁)
    (h₂ : IsFlowLine κ b jumps x θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) := by
  have e5 := hW5 κ hκ hκ4 b jumps hb x x θ₁ θ₂ le_rfl hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have e2a := hW2a κ hκ hκ4 b jumps hb x x θ₁ θ₂ le_rfl hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [e5, e2a, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_apply_zero_of_isFlowLine h₁,
    ae_apply_zero_of_isFlowLine h₂] with ω hord hfr hi₁ h0₁ h0₂
  refine contactsIncreasing_of_strict_of_frontier hi₁ ?_ ?_
  · intro s s' t t' hs hs' ht ht' hst hst' hlt
    exact (contacts_strict_increasing_of_completions hG5 h0₁ h0₂ hord hs hs' ht ht' hst hst').mp hlt
  · intro A B hA hB
    exact hfr A B hA hB fun a c ha hc =>
      hord a c ((ENNReal.coe_lt_coe.mpr ha).trans_le hA) ((ENNReal.coe_lt_coe.mpr hc).trans_le hB)

/-- **Lemma W6** (p. 537), from W5, W2a, G5 and Aux. 25: "Label the lower-angle curve `α` and the higher-angle curve
`β`. Every pair of strict prefixes has ordered proper completions by W5. The contact-order theorem G5 for these
completions therefore orders every contact whose two parameters are strictly below their lifetimes"; the remaining
reversed pairs use a finite threshold and are excluded as in W2a. -/
theorem w6Statement_of_inputs (hW5 : W5Statement.{u}) (hW2a : W2aStatement.{u}) (hG5 : G5Statement)
    (hA25 : Aux25Statement.{u}) : W6Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ₁ θ₂ hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  rcases lt_or_gt_of_ne hθ with hlt | hgt
  · exact w6_of_lt hW5 hW2a hG5 hA25 hκ hκ4 hb hlt hh h₁ h₂
  · filter_upwards [w6_of_lt hW5 hW2a hG5 hA25 hκ hκ4 hb hgt hh h₂ h₁,
      ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁] with ω hω hi₁
    exact hω.swap hi₁

/-! ### Theorem W8 -/

/-- **Theorem W8, common selection, no return** (supplement §10, pp. 539–540) for the canonical pair from one seed
(the chart form used in its proof): "Apply W6 to the common-seed canonical pair […]. If it is nonempty, choose one
finite contact `(u_*, v_*)`. Both coordinate minima are attained in the compact rectangle `[0, u_*] × [V, v_*]`.
Increasing order makes them a single pair `(u₀, v₀)` and hence a common point `q`. […] Increasing contact order and
simplicity give (W8.2)." For every start `σ` of the second path: the later contact relation, if nonempty, has a
coordinatewise least element `(u₀, v₀)`, and neither available tail after it returns to
`η₁([0, u₀]) ∪ η₂([0, v₀])`. -/
def W8CommonSeedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x θ₁ θ₂ : ℝ, θ₁ ≠ θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ σ : ℝ≥0∞, (laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω)).Nonempty →
        ∃ p ∈ laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω),
          (∀ q ∈ laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω), p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∧
          (∀ s : ℝ≥0, p.1 < s → (s : ℝ≥0∞) ≤ ζ₁ ω →
            η₁ ω s ∉ η₁ ω '' Icc 0 p.1 ∪ η₂ ω '' Icc 0 p.2) ∧
          ∀ t : ℝ≥0, p.2 < t → (t : ℝ≥0∞) ≤ ζ₂ ω →
            η₂ ω t ∉ η₁ ω '' Icc 0 p.1 ∪ η₂ ω '' Icc 0 p.2

/-- The pathwise core of W8's selection: continuous injective available curves with increasing contacts have, for
every start `σ`, a least later contact, after which neither tail returns. -/
theorem w8_selection_of_contactsIncreasing {α β : ℝ≥0 → ℂ} {T₁ T₂ : ℝ≥0∞}
    (hα : ContinuousOn α {s | (s : ℝ≥0∞) ≤ T₁}) (hβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ T₁}) (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ T₂})
    (hinc : ContactsIncreasing α T₁ β T₂) (σ : ℝ≥0∞)
    (hne : (laterContactSet α T₁ β σ T₂).Nonempty) :
    ∃ p ∈ laterContactSet α T₁ β σ T₂,
      (∀ q ∈ laterContactSet α T₁ β σ T₂, p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∧
      (∀ s : ℝ≥0, p.1 < s → (s : ℝ≥0∞) ≤ T₁ → α s ∉ α '' Icc 0 p.1 ∪ β '' Icc 0 p.2) ∧
      ∀ t : ℝ≥0, p.2 < t → (t : ℝ≥0∞) ≤ T₂ → β t ∉ α '' Icc 0 p.1 ∪ β '' Icc 0 p.2 := by
  obtain ⟨p, hp, hle⟩ := exists_least_laterContactSet_of_contactsIncreasing hα hβ hβi hinc hne
  have hnr := no_return_of_contactsIncreasing hαi hβi hinc (u₀ := p.1) (v₀ := p.2)
    (laterContactSet_subset_stoppedContactSet hp)
  exact ⟨p, hp, hle, hnr.1, hnr.2⟩

/-- **Theorem W8, common-seed selection** from W6 and Aux. 25. -/
theorem w8CommonSeedStatement_of_w6 (hW6 : W6Statement.{u}) (hA25 : Aux25Statement.{u}) :
    W8CommonSeedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ₁ θ₂ hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [hW6 κ hκ hκ4 b jumps hb x θ₁ θ₂ hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₂,
    ae_continuousOn_of_isFlowLine h₁, ae_continuousOn_of_isFlowLine h₂] with ω hinc hi₁ hi₂ hc₁ hc₂
  exact fun σ hne => w8_selection_of_contactsIncreasing hc₁ hc₂ hi₁ hi₂ hinc σ hne

/-- **Theorem W8 at `σ = 0`** (the Theorem 1.5 input; supplement p. 539: "Suppose instead their finite global first
contact is `w = α₁(a₁) = α₂(a₂)`. The established first-contact theorem supplies the retained kernel, common active
prime end, confinement, old-union avoidance and actual conditional continuation couplings. If `σ ≤ a₂`, the later
selection is exactly this first contact"), from Lemma 7.7. -/
theorem w8FirstContactStatement_of_lemma77 (h77 : Lemma77Statement.{u}) : W8FirstContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂] with ω hω hc
  obtain ⟨s₀, t₀, h₀, -⟩ := hω hc
  exact ⟨s₀, t₀, h₀⟩

end Supp10

end InteractingSLE
