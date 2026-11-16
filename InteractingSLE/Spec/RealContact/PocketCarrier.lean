/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.Statements
import InteractingSLE.Spec.Supplement.G7Carrier

/-!
# The pocket corner: the missing conditional law, as a kernel carrier

Packet PROVE-RC-POCKET (ruling R124). `RealContact.PocketCornerStatement` (`Hit.lean`) says: for the lower-angle flow
line `η₁` from `x₁` and the higher-angle flow line `η₂` from `x₂ ≤ x₁` at a critical angle gap ((7.12D.1)), almost
surely `η₂` does not end at a real point `q < x₂` which `η₁` visits before its lifetime. This file states the one
conditional law which the proof needs and which the project does not have, **as a named input; it is not proved in
Lean**. `PocketMain.lean` proves the pocket-corner exclusion from it.

## The route (role-swapped Lemma G7)

Retain the **second** path through its lifetime `T = ζ₂` and nothing of the first path (the retained pair `(0, ζ₂)`).
On the event that `η₂` ends at a real point `e < x₂`, the complement of the completed path has an unbounded component
`D`, and the first path lies in its closure until it first meets `η₂([0, T])` again. Conditionally on the completed
second path, the field in `D`, read in the chart of `D` centred at the terminal point `e` (the centred Loewner map of
`η₂` at its lifetime), is a GFF with a finite boundary word, and the first path is its angle-`θ₁` flow line from the
chart position `w > 0` of `x₁`. This is Lemma G7 (specification supplement §7.6, pp. 497–498) for the retained pair
`(0, ζ₂)`, and Lemma SB2(2) (supplement p. 631) at the first stage of the lower walk. The landed
`Supp7.G7RetainedPairStatement` covers deterministic cutoffs with two interior tips only.

In that chart the terminal point `e` is the point `0`: the junction of the untouched real line `(−∞, e)`, which keeps
its original height (the chart is real and increasing there, so the lift vanishes), with the exposed right side of
`η₂`. If the first path visits `e` before its lifetime, its left cumulative weight just beyond `0` exceeds `−2`, hence
`κ/2 − 4`, and Lemma G12 for the conditional flow excludes the visit, terminal endpoint included.

## Why the statement is not vacuous

The pathwise clause is required on the event "`η₂` ends at a real point `e < x₂` and `η₁` visits a real point
`y ≤ e` before its lifetime". This event has positive probability in general (`η₁` passes over the completed `η₂`
and touches the real line to the left of it), unlike the pocket corner `y = e` itself. On it the clause describes
the whole first path up to and including its first new contact with `η₂([0, T])`: chart, inverse, lift, the chart
field of `h`, and the clock, as in `Supp7.IsRetainedContinuation`. The visit of a real point `y ≤ e` makes the first
seed active: a first path trapped in a bounded component of `ℍ \ η₂([0, T])` could reach the real line only inside the
base `[e, ·]` of the hull, and by W5 it does not lie on the left of `η₂`.

## Statements

* `IsTerminalRetainedContinuation` — the pathwise relation;
* `TerminalRetainedPairStatement` — the named input (**not proved in Lean**).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace RealContact

open Restart Theorem15D5

open PiecewiseConstantBoundaryData (leftLim)

/-- **The first path read in the chart of the completed second path** (Lemma G7, supplement pp. 497–498, at the
retained pair `(0, T)` with `T` the second path's lifetime). With `D = activeDomain η₁ 0 η₂ T`, the unbounded
component of `ℍ \ η₂([0, T])`:
* `φ` is a chart of `D` centred at the terminal point `η₂(T)`, `ψ` its inverse on `ℍ` (values off `ℍ` lie off `D`),
  `lift` a continuous branch of `arg φ′`, and `H` is the field `h` in the chart (frozen `IsChartTransport`, `σ = 1`,
  `a = 0`, `k = χ`);
* the clock `c₁` is strictly increasing on the chart times `[0, σ]`, `σ ≤ U`, and maps them onto the physical times
  `t ≤ ζ₁` with no contact with `η₂([0, T])` strictly between `0` and `t` (the first path up to and including its
  first new contact with the completed second path), and `η₁ ∘ c₁ = ψ ∘ Γ` there;
* (the junction) the chart path is at `0` whenever the first path is at the terminal point `η₂(T)`: the chart is
  centred there, and the terminal point has one chart preimage;
* (the untouched side) the datum `c` just left of `0` is the original datum just left of the terminal point: the
  chart is real and increasing on the untouched real line left of the terminal point, with zero lift. -/
def IsTerminalRetainedContinuation (κ : ℝ) (b : ℝ → ℝ) (h H : LQGMetric.DistOn upperHalfPlaneOpens)
    (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (η₂ : ℝ≥0 → ℂ) (T : ℝ≥0) (c : BoundaryWord) (Γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) :
    Prop :=
  ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (c₁ : ℝ≥0 → ℝ≥0) (σ : ℝ≥0∞),
    IsActiveChart (activeDomain η₁ 0 η₂ T) (η₂ T) φ ∧
    BijOn ψ QuantumZipper.H (activeDomain η₁ 0 η₂ T) ∧ (∀ w ∈ QuantumZipper.H, φ (ψ w) = w) ∧
    (∀ w ∉ QuantumZipper.H, ψ w ∉ activeDomain η₁ 0 η₂ T) ∧
    ContinuousOn lift (activeDomain η₁ 0 η₂ T) ∧
    (∀ z ∈ activeDomain η₁ 0 η₂ T,
      deriv φ z = (‖deriv φ z‖ : ℂ) * Complex.exp (Complex.I * (lift z : ℂ))) ∧
    IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H ∧
    σ ≤ U ∧ StrictMonoOn c₁ {s | (s : ℝ≥0∞) ≤ σ} ∧
    c₁ '' {s | (s : ℝ≥0∞) ≤ σ} =
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁ ∧ ∀ t' : ℝ≥0, 0 < t' → t' < t → η₁ t' ∉ η₂ '' Icc 0 T} ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ (c₁ s) = ψ (Γ s)) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₁ (c₁ s) = η₂ T → Γ s = 0) ∧
    leftLim c.fn 0 = leftLim b (η₂ T).re

/-- **Named input: Lemma G7 at the retained pair `(0, ζ₂)`, as a kernel carrier** (specification supplement §7.6,
Lemma G7, pp. 497–498, with the second path retained through its lifetime; Lemma SB2(2), p. 631, at the first stage).
Setting of `G7GB7aFirstHitRealStatement`: `η₁` the angle-`θ₁` flow line from `x₁`, `η₂` the angle-`θ₂` flow line from
`x₂ ≤ x₁`, with (7.12D.1). There are a canonical space `S : Type` with measurable coordinates (chart field `H`, chart
path `Γ` continuous on its closed available interval, lifetime `U`), a measurable event `M`, a measurable datum
`β = (word, chart position of the first seed)`, a measurable restart variable `X` and a Markov kernel `K` with
* `K` the conditional law of `X` given `β` on `M`;
* for almost every datum `(c, w)`: `w > 0`, and under `K (c, w)` the field `H` is a GFF with datum `c` and `Γ`
  (lifetime `U`) is its angle-`θ₁` flow line from `w`;
* almost surely, if `η₂` ends at a real point `e < x₂` (`T = ζ₂` finite, `η₂(T) = e`) and `η₁` visits a real point
  `y ≤ e` before its lifetime, then `ω ∈ M` and `IsTerminalRetainedContinuation` holds for `X ω`, `β ω`.

**Not proved in Lean.** See the module docstring for the event (it has positive probability) and
`planning/handoffs/PROVE-RC-POCKET.md` for the mathematical proof. -/
def TerminalRetainedPairStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ : S → ℝ≥0 → ℂ)
      (U : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S) (K : Kernel (BoundaryWord × ℝ) S),
      Measurable H ∧ Measurable U ∧ (∀ t : ℝ≥0, Measurable fun s => Γ s t) ∧
      (∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) ∧
      MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ d ∂(P.restrict M).map β, 0 < d.2 ∧
        IsGFFWithBoundaryData (K d) H d.1.fn d.1.jumps ∧ IsFlowLine κ d.1.fn d.1.jumps d.2 θ₁ (K d) H Γ U) ∧
      ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (e : ℝ), (T : ℝ≥0∞) = ζ₂ ω → η₂ ω T = e → e < x₂ →
        (∃ (s : ℝ≥0) (y : ℝ), (s : ℝ≥0∞) < ζ₁ ω ∧ η₁ ω s = y ∧ y ≤ e) →
        ω ∈ M ∧ IsTerminalRetainedContinuation κ b (h ω) (H (X ω)) (η₁ ω) (ζ₁ ω) (η₂ ω) T (β ω).1
          (Γ (X ω)) (U (X ω))

end RealContact

end InteractingSLE
