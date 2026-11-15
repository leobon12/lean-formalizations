/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCKG8Law
import InteractingSLE.Spec.Supplement.G7RetainedReduce

/-!
# Lemma G9 at a retained pair of a complete ordered reference (the deterministic lift)

Packet PROVE-RLC-K, item (f) of `planning/handoffs/PROVE-RLC-G.md`. Source: Lemma G9 and its proof (supplement §7.8,
pp. 501–502, `source/spec/p481-528.md` L495–L510): "Take […] a complete physical ordered reference underlying G8.
Retain two finite prefixes with distinct interior active tips, each off the other retained prefix […] Consider the
event that they have a common physical point `q ∉ A` […] On this event, the two complete fresh reference tails […]
lie in the closure of the initial joint unbounded component. In its inherited chart they have continuous injective
proper lifts, and these lifts are ordered with the higher-angle path on the left."

The statement is deterministic: one complete ordered pair `(α, β)` from the common seed `0`, an ordinary retained
pair at the cutoffs `(u, r)`, its chart `(φ, ψ)` (G7's `IsRetChart`, tip of `β` at `0`, tip of `α` at `w`), the chart
real points beyond `v` lying over untouched original real points (the good frame of G8's proof), and the two chart
continuations read through the chart up to their first new contact with the retained union (`IsRetainedClock`).
Conclusion: every pair of chart prefixes before the chart lifetimes, with real points (after time `0`) beyond `v` and a
common point, is completable (`RefCompletable (Ioi v)`).

* `G9LiftStatement` (**named here, proved in `RLCKLiftProof.lean`**, deterministic). Besides the source's data it
  records three facts that hold almost surely for flow lines and that the deterministic proof uses: both complete curves
  are good paths (`IsPathGood`, Aux. 25 and the generating trace), the chart is the hydrodynamic one, and no positive
  rational real point is on the first curve (Lemma 7.16, point form; only used to find one untouched real point right
  of the first tip that the first curve does not visit).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Supp7

/-- **Named statement: Lemma G9 for the complete ordered reference of G8, at one retained pair** (supplement
pp. 501–502; deterministic). Let `(α, β)` be a complete ordered pair (`β` in the closed left side of `α`) from the
common seed `0`, ordinary at the cutoffs `(u, r)` (both tips interior, each off the other prefix, jointly active),
with chart `(φ, ψ)` (`IsRetChart`, `ψ 0 = β(r)`, `ψ w = α(u)`), whose real points beyond `v` lie over original real
points off the retained union `A = α[0, u] ∪ β[0, r]`; let `Γ₁`, `Γ₂` be continuous chart paths in `ℍ̄` from `w` and
`0` read through `ψ` up to the first new contact of `α`, `β` with `A` (`IsRetainedClock`). Then every pair of chart
prefixes strictly before the chart lifetimes, with real points (after time `0`) beyond `v` and a common point after
time `0`, is completable.

**Proof plan (source).** (i) An admissible chart prefix ends strictly before the first new contact (`lt_sigma_of_adm`).
(ii) The common chart point lies over a common physical point `q ∉ A` of the two continuations; by the contact order
of the complete ordered pair (`Supp9B.contact_order`) and injectivity, neither complete tail after its cutoff meets
`A`, so both tails lie in the unbounded component of `ℍ̄ \ A` (in `D` or on untouched real points). (iii) The chart
extends continuously to the untouched real points (regular points of `IsFirstContactChart`) and is injective there;
the lifts of the tails, glued to the chart prefixes, are continuous injective proper curves (`‖φ(z) − z‖ ≤ M`).
(iv) Order: a component of the chart right side of the lifted first curve pulls back into the physical right side of
`α` (Jordan sides, orientation of the collar of an interior subarc), which `β` avoids; the real points follow by
continuity (`image_side_subset`-type transfer, `RLCCGlue`). (v) The lifted tails avoid the other chart seed: its
inverse image is the other tip, in `A`. -/
def G9LiftStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (u r : ℝ≥0) (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (w v : ℝ) (Γ₁ Γ₂ : ℝ≥0 → ℂ)
    (U₁ U₂ : ℝ≥0∞),
    Sec7.Prop74Order.IsCompleteOrderedPair α β → α 0 = 0 → β 0 = 0 →
    Restart.IsPathGood α ⊤ 0 → Restart.IsPathGood β ⊤ 0 →
    (∀ q : ℚ, 0 < (q : ℝ) → ((q : ℝ) : ℂ) ∉ range α) →
    IsOrdinaryRetainedPair α ⊤ u β ⊤ r → IsRetChart α u β r φ ψ lift →
    (∃ x₀ : ℝ, ∀ z, φ z = ConformalImage.mapOut (fillH (Restart.prefixSet α u β r)) z - x₀) → ψ w = α u → 0 < w →
    (∀ y : ℝ, v < y → (ψ y).im = 0 ∧ 0 < (ψ y).re ∧ ψ y ∉ α '' Icc 0 u ∪ β '' Icc 0 r) →
    IsRetainedClock α ⊤ u (α '' Icc 0 u ∪ β '' Icc 0 r) ψ Γ₁ U₁ →
    IsRetainedClock β ⊤ r (α '' Icc 0 u ∪ β '' Icc 0 r) ψ Γ₂ U₂ →
    Γ₁ 0 = w → Γ₂ 0 = 0 → ContinuousOn Γ₁ {t | (t : ℝ≥0∞) ≤ U₁} → ContinuousOn Γ₂ {t | (t : ℝ≥0∞) ≤ U₂} →
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < U₁ → Γ₁ t ∈ Hbar) → (∀ t : ℝ≥0, (t : ℝ≥0∞) < U₂ → Γ₂ t ∈ Hbar) →
    RefCompletable (Ioi v) Γ₁ U₁ Γ₂ U₂

end RLC

end InteractingSLE
