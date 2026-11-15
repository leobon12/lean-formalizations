/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9Propagation

/-!
# Supplement §9: Lemma W2a (a reversed frontier pair is also excluded)

Packet PROVE-SUPP9 (specification supplement §9, `source/spec/p529-576.md` L130–L139, p. 533).

"Suppose that, for continuous increasing clocks `A(u), B(u)`, every pair of prefixes at `u < τ` has ordered proper
completions. Consider contacts in the rectangle `[0, A(τ)] × [0, B(τ)]`. The new contacts on its top or right edge
cannot reverse the increasing order of the contacts in its strict interior, nor can the two new edge contacts be
distinct and reverse one another."

The proof splits into three cases; this file proves the case analysis, pathwise, from the events it excludes:

* a top-edge contact backwards relative to a strict-interior contact is the W1 configuration
  (`IsW1Configuration`, excluded by W2), with the cuts' prefixes strictly below the frontier;
* a right-edge contact backwards relative to a strict-interior contact is the W1 configuration "with the paths and
  left/right orientations exchanged" (`IsW1ConfigurationSwap`, excluded by W2 in that orientation);
* two distinct edge contacts, each forward relative to all earlier contacts (`IsW2aCornerConfiguration`), are
  excluded by the second paragraph of W2a's proof ("The activity and retained-law proof of W2 applies unchanged, and
  Lemma 7.7 contradicts this empty lower rectangle").

For linear clocks `A(u) = uA`, `B(u) = uB` the hypothesis "every pair of prefixes at `u < τ`" is, by heredity, the
same as "every pair `a < A`, `c < B`". The conclusion `NoReversedFrontierPair` and `W2aStatement` are stated exactly
as the named input `W2aStatement` of PROVE-SUPP10 (`Spec/Supplement/S10Main.lean`, `S10Order.lean`), so that input
can be discharged by `w2aStatement_of_inputs` once the two copies are identified at integration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp9

/-- The configuration of **Lemma W1 with the paths and left/right orientations exchanged** (p. 530: "The same
conclusion holds with the paths and left/right orientations exchanged"): an ordered history
`𝓔(α([0, u]), β([0, B]))` for every `u < T`, a new contact `p = α(T) = β(b)` at the end of the first prefix and an
earlier contact `α(a) = β(v)` with `a < T`, `0 < b < v ≤ B`, no common open subarc before `T`, and `p` not an original
seed. Excluded by W2 in this orientation. -/
def IsW1ConfigurationSwap (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∃ T B b v a : ℝ≥0, (T : ℝ≥0∞) ≤ ζ₁ ∧ (B : ℝ≥0∞) ≤ ζ₂ ∧
    (∀ u < T, HasOrderedProperCompletions α u β B) ∧ α T = β b ∧ α a = β v ∧
    0 < b ∧ b < v ∧ v ≤ B ∧ a < T ∧ (∀ u < T, ¬ HasCommonOpenSubarc α u β B) ∧
    α T ≠ α 0 ∧ α T ≠ β 0

/-- The configuration excluded by the second paragraph of **Lemma W2a's proof** (p. 533): "two distinct new contacts
`(a, B(τ))` and `(A(τ), b)` which are each forward relative to all earlier contacts. Then every earlier contact has
coordinates strictly below `a, b`", after an ordered history on the strict rectangle. -/
def IsW2aCornerConfiguration (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∃ A B a b : ℝ≥0, (A : ℝ≥0∞) ≤ ζ₁ ∧ (B : ℝ≥0∞) ≤ ζ₂ ∧
    (∀ a' c : ℝ≥0, a' < A → c < B → HasOrderedProperCompletions α a' β c) ∧
    a < A ∧ b < B ∧ α a = β B ∧ α A = β b ∧ α a ≠ α A ∧
    ∀ s v : ℝ≥0, s < A → v < B → α s = β v → s < a ∧ v < b

/-- **The conclusion of Lemma W2a** on the rectangle `[0, A] × [0, B]` (identical to PROVE-SUPP10's
`NoReversedFrontierPair`): a top-edge contact `(a, B)` does not reverse a strict-interior contact `(b, v)`, a
right-edge contact `(A, b)` does not reverse a strict-interior contact `(a, v)`, and two edge contacts `(a, B)`,
`(A, b)` with `a < A`, `b < B` are not at distinct points. -/
def NoReversedFrontierPair (α : ℝ≥0 → ℂ) (A : ℝ≥0) (β : ℝ≥0 → ℂ) (B : ℝ≥0) : Prop :=
  (∀ a b v : ℝ≥0, a ≤ A → b < A → v < B → α a = β B → α b = β v → ¬ a < b) ∧
    (∀ b a v : ℝ≥0, b ≤ B → a < A → v < B → α A = β b → α a = β v → ¬ b < v) ∧
    ∀ a b : ℝ≥0, a < A → b < B → α a = β B → α A = β b → α a ≠ α A → False

section Pathwise

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

theorem zero_mem_setOf_coe_le (ζ : ℝ≥0∞) : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} :=
  show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ by rw [ENNReal.coe_zero]; exact zero_le

/-- **Lemma W2a, pathwise** (p. 533): the three cases of the proof, from the exclusion of the two W1 configurations
(W2), of the corner configuration, W0b, and the seed facts (W0a or a common seed). -/
theorem noReversedFrontierPair_of_inputs (hαi : InjOn α {s | (s : ℝ≥0∞) ≤ ζ₁})
    (hβi : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂}) (hW2 : ¬ IsW1Configuration α ζ₁ β ζ₂)
    (hW2s : ¬ IsW1ConfigurationSwap α ζ₁ β ζ₂) (hcorner : ¬ IsW2aCornerConfiguration α ζ₁ β ζ₂)
    (hW0b : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions α a β c →
      ¬ HasCommonOpenSubarc α a β c)
    (hseed : 0 < ζ₁ → 0 < ζ₂ → α 0 = β 0 ∨
      ((∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ → β t ≠ α 0) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ → α s ≠ β 0))
    {A B : ℝ≥0} (hA : (A : ℝ≥0∞) ≤ ζ₁) (hB : (B : ℝ≥0∞) ≤ ζ₂)
    (hE : ∀ a c : ℝ≥0, a < A → c < B → HasOrderedProperCompletions α a β c) :
    NoReversedFrontierPair α A β B := by
  -- a top-edge contact backwards relative to a strict-interior contact (W1–W2)
  have c1 : ∀ a b v : ℝ≥0, a ≤ A → b < A → v < B → α a = β B → α b = β v → ¬ a < b := by
    intro a b v _ hbA hvB hp hq hab
    have hB0 : 0 < B := lt_of_le_of_lt zero_le hvB
    have hζ₁ : 0 < ζ₁ := lt_of_lt_of_le (ENNReal.coe_pos.2 (lt_of_le_of_lt zero_le hbA)) hA
    have hζ₂ : 0 < ζ₂ := lt_of_lt_of_le (ENNReal.coe_pos.2 hB0) hB
    have hβB : β B ≠ β 0 := fun h => (ne_of_gt hB0) (hβi hB (zero_mem_setOf_coe_le ζ₂) h)
    have hs1 : α a ≠ α 0 := by
      rw [hp]
      rcases hseed hζ₁ hζ₂ with h | h
      · rw [h]
        exact hβB
      · exact h.1 B hB
    have ha0 : 0 < a := pos_iff_ne_zero.2 fun h => hs1 (by rw [h])
    have hbζ : (b : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hbA).trans_le hA
    exact hW2 ⟨b, B, a, b, v, hbζ.le, hB, fun v' hv' => hE b v' hbA hv', hp, hq, ha0, hab, le_rfl, hvB,
      fun v' hv' => hW0b b v' hbζ ((ENNReal.coe_lt_coe.2 hv').trans_le hB) (hE b v' hbA hv'), hs1,
      by rw [hp]; exact hβB⟩
  -- a right-edge contact backwards relative to a strict-interior contact (W1–W2, exchanged)
  have c2 : ∀ b a v : ℝ≥0, b ≤ B → a < A → v < B → α A = β b → α a = β v → ¬ b < v := by
    intro b a v _ haA hvB hp hq hbv
    have hA0 : 0 < A := lt_of_le_of_lt zero_le haA
    have hζ₁ : 0 < ζ₁ := lt_of_lt_of_le (ENNReal.coe_pos.2 hA0) hA
    have hζ₂ : 0 < ζ₂ := lt_of_lt_of_le (ENNReal.coe_pos.2 (lt_of_le_of_lt zero_le hvB)) hB
    have hαA : α A ≠ α 0 := fun h => (ne_of_gt hA0) (hαi hA (zero_mem_setOf_coe_le ζ₁) h)
    have hs2 : α A ≠ β 0 := by
      rcases hseed hζ₁ hζ₂ with h | h
      · rw [← h]
        exact hαA
      · exact h.2 A hA
    have hb0 : 0 < b := pos_iff_ne_zero.2 fun h => hs2 (by rw [hp, h])
    have hvζ : (v : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hvB).trans_le hB
    exact hW2s ⟨A, v, b, v, a, hA, hvζ.le, fun u hu => hE u v hu hvB, hp, hq, hb0, hbv, le_rfl, haA,
      fun u hu => hW0b u v ((ENNReal.coe_lt_coe.2 hu).trans_le hA) hvζ (hE u v hu hvB), hαA, hs2⟩
  refine ⟨c1, c2, fun a b haA hbB hp hq hne => hcorner ⟨A, B, a, b, hA, hB, hE, haA, hbB, hp, hq, hne,
    fun s v hsA hvB hsv => ⟨not_le.1 fun h => ?_, not_le.1 fun h => ?_⟩⟩⟩
  · rcases h.lt_or_eq with h | h
    · exact c1 a s v haA.le hsA hvB hp hsv h
    · have : v = B := hβi ((ENNReal.coe_lt_coe.2 hvB).trans_le hB).le hB (by rw [← hsv, ← h, hp])
      exact (ne_of_lt hvB) this
  · rcases h.lt_or_eq with h | h
    · exact c2 b s v hbB.le hsA hvB hq hsv h
    · have : s = A := hαi ((ENNReal.coe_lt_coe.2 hsA).trans_le hA).le hA (by rw [hsv, ← h, hq])
      exact (ne_of_lt hsA) this

end Pathwise

/-! ### The almost-sure statements -/

section Statements

/-- **Named input: Lemma W2 in the exchanged orientation** (p. 530; W1: "The same conclusion holds with the paths
and left/right orientations exchanged"; used by W2a, p. 533): the exchanged W1 event has probability zero. **Not
proved in Lean** (same obstruction as `W2Statement`). -/
def W2SwapStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ¬ IsW1ConfigurationSwap (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)

/-- **Named input: Lemma W2a's proof, the two forward edge contacts** (p. 533): "Choose rational cuts inside this
gap below `a, b`. The two fresh histories contain the two new contacts but have no contact in the rectangle below
`(a, b)`. The activity and retained-law proof of W2 applies unchanged, and Lemma 7.7 contradicts this empty lower
rectangle." **Not proved in Lean** (same obstruction as `W2Statement`). -/
def W2aCornerStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ¬ IsW2aCornerConfiguration (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)

/-- **Lemma W2a** (a reversed frontier pair is also excluded, p. 533), for the flow lines of W5 and linear clocks,
stated exactly as PROVE-SUPP10's named input `W2aStatement`: almost surely, for every rectangle `[0, A] × [0, B]`
inside the available ranges whose strict prefix pairs all have ordered proper completions, no frontier pair is
reversed. -/
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

end Statements

/-- **Lemma W2a** from Aux. lemma 25 (simplicity), W0a, W0b, W2 in both orientations and the corner exclusion (a
conditional helper: the last five are §9 statements not proved in Lean; the case analysis is proved). -/
theorem w2aStatement_of_inputs (h25 : Theorem15.Aux25Statement.{u}) (hW0a : W0aStatement.{u})
    (hW0b : W0bStatement.{u}) (hW2 : W2Statement.{u}) (hW2s : W2SwapStatement.{u})
    (hC : W2aCornerStatement.{u}) : W2aStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hW0a' : ∀ᵐ ω ∂P, x₂ < x₁ → 0 < ζ₁ ω → 0 < ζ₂ ω →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁) ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω s ≠ x₂) := by
    by_cases hlt : x₂ < x₁
    · filter_upwards [hW0a κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hlt hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
        with ω hω _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hlt
  filter_upwards [Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₁,
    Theorem15.ae_injOn_of_isFlowLine h25 hκ hκ4 hη₂,
    ae_apply_zero_of_isFlowLine hη₁, ae_apply_zero_of_isFlowLine hη₂, hW0a',
    hW0b κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hW2 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hW2s κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hC κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
    with ω hi₁ hi₂ h0₁ h0₂ ha hb0 hw2 hw2s hc A B hA hB hE
  refine noReversedFrontierPair_of_inputs hi₁ hi₂ hw2 hw2s hc hb0 (fun h1 h2 => ?_) hA hB hE
  rcases hx.lt_or_eq with hlt | heq
  · obtain ⟨hv₂, hv₁⟩ := ha hlt h1 h2
    exact Or.inr ⟨fun t ht => by rw [h0₁]; exact hv₂ t ht, fun s hs => by rw [h0₂]; exact hv₁ s hs⟩
  · exact Or.inl (by rw [h0₁, h0₂, heq])

end Supp9

end InteractingSLE
